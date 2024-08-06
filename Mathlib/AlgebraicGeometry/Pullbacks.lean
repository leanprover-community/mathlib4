/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

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
  pullback ((pullback.fst (𝒰.map i ≫ f) g) ≫ 𝒰.map i) (𝒰.map j)

/-- The canonical transition map `(Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ` given by the fact
that pullbacks are associative and symmetric. -/
def t (i j : 𝒰.J) : v 𝒰 f g i j ⟶ v 𝒰 f g j i := by
  have : HasPullback (pullback.snd _ _ ≫ 𝒰.map i ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map j) (𝒰.map i) (𝒰.map i ≫ f) g
  have : HasPullback (pullback.snd _ _ ≫ 𝒰.map j ≫ f) g :=
    hasPullback_assoc_symm (𝒰.map i) (𝒰.map j) (𝒰.map j ≫ f) g
  refine (pullbackSymmetry ..).hom ≫ (pullbackAssoc ..).inv ≫ ?_
  refine ?_ ≫ (pullbackAssoc ..).hom ≫ (pullbackSymmetry ..).hom
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · rw [pullbackSymmetry_hom_comp_snd_assoc, pullback.condition_assoc, Category.comp_id]
  · rw [Category.comp_id, Category.id_comp]

@[simp, reassoc]
theorem t_fst_fst (i j : 𝒰.J) : t 𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
    pullback.snd _ _ := by
  simp only [t, Category.assoc, pullbackSymmetry_hom_comp_fst_assoc, pullbackAssoc_hom_snd_fst,
    pullback.lift_fst_assoc, pullbackSymmetry_hom_comp_snd, pullbackAssoc_inv_fst_fst,
    pullbackSymmetry_hom_comp_fst]

@[simp, reassoc]
theorem t_fst_snd (i j : 𝒰.J) :
    t 𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t, Category.assoc, pullbackSymmetry_hom_comp_fst_assoc, pullbackAssoc_hom_snd_snd,
    pullback.lift_snd, Category.comp_id, pullbackAssoc_inv_snd, pullbackSymmetry_hom_comp_snd_assoc]

@[simp, reassoc]
theorem t_snd (i j : 𝒰.J) : t 𝒰 f g i j ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [t, Category.assoc, pullbackSymmetry_hom_comp_snd, pullbackAssoc_hom_fst,
    pullback.lift_fst_assoc, pullbackSymmetry_hom_comp_fst, pullbackAssoc_inv_fst_snd,
    pullbackSymmetry_hom_comp_snd_assoc]

theorem t_id (i : 𝒰.J) : t 𝒰 f g i i = 𝟙 _ := by
  apply pullback.hom_ext <;> rw [Category.id_comp]
  · apply pullback.hom_ext
    · rw [← cancel_mono (𝒰.map i)]; simp only [pullback.condition, Category.assoc, t_fst_fst]
    · simp only [Category.assoc, t_fst_snd]
  · rw [← cancel_mono (𝒰.map i)]; simp only [pullback.condition, t_snd, Category.assoc]

/-- The inclusion map of `V i j = (Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ Uᵢ ×[Z] Y`-/
abbrev fV (i j : 𝒰.J) : v 𝒰 f g i j ⟶ pullback (𝒰.map i ≫ f) g :=
  pullback.fst _ _

/-- The map `((Xᵢ ×[Z] Y) ×[X] Xⱼ) ×[Xᵢ ×[Z] Y] ((Xᵢ ×[Z] Y) ×[X] Xₖ)` ⟶
  `((Xⱼ ×[Z] Y) ×[X] Xₖ) ×[Xⱼ ×[Z] Y] ((Xⱼ ×[Z] Y) ×[X] Xᵢ)` needed for gluing   -/
def t' (i j k : 𝒰.J) :
    pullback (fV 𝒰 f g i j) (fV 𝒰 f g i k) ⟶ pullback (fV 𝒰 f g j k) (fV 𝒰 f g j i) := by
  refine (pullbackRightPullbackFstIso ..).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso ..).inv
  refine pullback.map _ _ _ _ (t 𝒰 f g i j) (𝟙 _) (𝟙 _) ?_ ?_
  · simp_rw [Category.comp_id, t_fst_fst_assoc, ← pullback.condition]
  · rw [Category.comp_id, Category.id_comp]

@[simp, reassoc]
theorem t'_fst_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
theorem t'_fst_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
theorem t'_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd, Category.comp_id,
    pullbackRightPullbackFstIso_hom_snd]

@[simp, reassoc]
theorem t'_snd_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
theorem t'_snd_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
theorem t'_snd_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]

theorem cocycle_fst_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
      pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [t'_fst_fst_fst, t'_fst_snd, t'_snd_snd]

theorem cocycle_fst_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
      pullback.snd _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t'_fst_fst_snd]

theorem cocycle_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t'_fst_snd, t'_snd_snd, t'_fst_fst_fst]

theorem cocycle_snd_fst_fst (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫
      pullback.fst _ _ = pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
  rw [← cancel_mono (𝒰.map i)]
  simp only [pullback.condition_assoc, t'_snd_fst_fst, t'_fst_snd, t'_snd_snd]

theorem cocycle_snd_fst_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [pullback.condition_assoc, t'_snd_fst_snd]

theorem cocycle_snd_snd (i j k : 𝒰.J) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp only [t'_snd_snd, t'_fst_fst_fst, t'_fst_snd]

-- `by tidy` should solve it, but it times out.
theorem cocycle (i j k : 𝒰.J) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j = 𝟙 _ := by
  apply pullback.hom_ext <;> rw [Category.id_comp]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp_rw [Category.assoc, cocycle_fst_fst_fst 𝒰 f g i j k]
      · simp_rw [Category.assoc, cocycle_fst_fst_snd 𝒰 f g i j k]
    · simp_rw [Category.assoc, cocycle_fst_snd 𝒰 f g i j k]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp_rw [Category.assoc, cocycle_snd_fst_fst 𝒰 f g i j k]
      · simp_rw [Category.assoc, cocycle_snd_fst_snd 𝒰 f g i j k]
    · simp_rw [Category.assoc, cocycle_snd_snd 𝒰 f g i j k]

/-- Given `Uᵢ ×[Z] Y`, this is the glued fibered product `X ×[Z] Y`. -/
@[simps U V f t t', simps (config := .lemmasOnly) J]
def gluing : Scheme.GlueData.{u} where
  J := 𝒰.J
  U i := pullback (𝒰.map i ≫ f) g
  V := fun ⟨i, j⟩ => v 𝒰 f g i j
  -- `p⁻¹(Uᵢ ∩ Uⱼ)` where `p : Uᵢ ×[Z] Y ⟶ Uᵢ ⟶ X`.
  f i j := pullback.fst _ _
  f_id i := inferInstance
  f_open := inferInstance
  t i j := t 𝒰 f g i j
  t_id i := t_id 𝒰 f g i
  t' i j k := t' 𝒰 f g i j k
  t_fac i j k := by
    apply pullback.hom_ext
    on_goal 1 => apply pullback.hom_ext
    all_goals
      simp only [t'_snd_fst_fst, t'_snd_fst_snd, t'_snd_snd, t_fst_fst, t_fst_snd, t_snd,
        Category.assoc]
  cocycle i j k := cocycle 𝒰 f g i j k

@[simp]
lemma gluing_ι (j : 𝒰.J) :
    (gluing 𝒰 f g).ι j = Multicoequalizer.π (gluing 𝒰 f g).diagram j := rfl

/-- The first projection from the glued scheme into `X`. -/
def p1 : (gluing 𝒰 f g).glued ⟶ X := by
  apply Multicoequalizer.desc (gluing 𝒰 f g).diagram _ fun i ↦ pullback.fst _ _ ≫ 𝒰.map i
  simp [t_fst_fst_assoc, ← pullback.condition]

/-- The second projection from the glued scheme into `Y`. -/
def p2 : (gluing 𝒰 f g).glued ⟶ Y := by
  apply Multicoequalizer.desc _ _ fun i ↦ pullback.snd _ _
  simp [t_fst_snd]

theorem p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f g ≫ g := by
  apply Multicoequalizer.hom_ext
  simp [p1, p2, pullback.condition]

variable (s : PullbackCone f g)

/-- (Implementation)
The canonical map `(s.X ×[X] Uᵢ) ×[s.X] (s.X ×[X] Uⱼ) ⟶ (Uᵢ ×[Z] Y) ×[X] Uⱼ`

This is used in `gluedLift`. -/
def gluedLiftPullbackMap (i j : 𝒰.J) :
    pullback ((𝒰.pullbackCover s.fst).map i) ((𝒰.pullbackCover s.fst).map j) ⟶
      (gluing 𝒰 f g).V ⟨i, j⟩ := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine pullback.map _ _ _ _ ?_ (𝟙 _) (𝟙 _) ?_ ?_
  · exact (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition
  · simpa using pullback.condition
  · simp only [Category.comp_id, Category.id_comp]

@[reassoc]
theorem gluedLiftPullbackMap_fst (i j : 𝒰.J) :
    gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫
        (pullbackSymmetry _ _).hom ≫
          pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition := by
  simp [gluedLiftPullbackMap]

@[reassoc]
theorem gluedLiftPullbackMap_snd (i j : 𝒰.J) :
    gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp [gluedLiftPullbackMap]

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
  · exact fun i ↦ (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition ≫ (gluing 𝒰 f g).ι i
  intro i j
  rw [← gluedLiftPullbackMap_fst_assoc, ← gluing_f, ← (gluing 𝒰 f g).glue_condition i j,
    gluing_t, gluing_f]
  simp_rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp_rw [Category.assoc]
  · rw [t_fst_fst, gluedLiftPullbackMap_snd]
    congr 1
    rw [← Iso.inv_comp_eq, pullbackSymmetry_inv_comp_snd, pullback.lift_fst, Category.comp_id]
  · rw [t_fst_snd, gluedLiftPullbackMap_fst_assoc, pullback.lift_snd, pullback.lift_snd]
    simp_rw [pullbackSymmetry_hom_comp_snd_assoc]
    exact pullback.condition_assoc _

theorem gluedLift_p1 : gluedLift 𝒰 f g s ≫ p1 𝒰 f g = s.fst := by
  rw [← cancel_epi (𝒰.pullbackCover s.fst).fromGlued]
  apply Multicoequalizer.hom_ext
  intro b
  simp_rw [OpenCover.fromGlued, Multicoequalizer.π_desc_assoc, gluedLift, ← Category.assoc]
  simp_rw [(𝒰.pullbackCover s.fst).ι_glueMorphisms]
  simp [p1, pullback.condition]

theorem gluedLift_p2 : gluedLift 𝒰 f g s ≫ p2 𝒰 f g = s.snd := by
  rw [← cancel_epi (𝒰.pullbackCover s.fst).fromGlued]
  apply Multicoequalizer.hom_ext
  intro b
  simp_rw [OpenCover.fromGlued, Multicoequalizer.π_desc_assoc, gluedLift, ← Category.assoc]
  simp_rw [(𝒰.pullbackCover s.fst).ι_glueMorphisms]
  simp [p2, pullback.condition]

/-- (Implementation)
The canonical map `(W ×[X] Uᵢ) ×[W] (Uⱼ ×[Z] Y) ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ = V j i` where `W` is
the glued fibred product.

This is used in `lift_comp_ι`. -/
def pullbackFstιToV (i j : 𝒰.J) :
    pullback (pullback.fst (p1 𝒰 f g) (𝒰.map i)) ((gluing 𝒰 f g).ι j) ⟶
      v 𝒰 f g j i :=
  (pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso (p1 𝒰 f g) (𝒰.map i) _).hom ≫
    (pullback.congrHom (Multicoequalizer.π_desc ..) rfl).hom

@[simp, reassoc]
theorem pullbackFstιToV_fst (i j : 𝒰.J) :
    pullbackFstιToV 𝒰 f g i j ≫ pullback.fst _ _ = pullback.snd _ _ := by
  simp [pullbackFstιToV, p1]

@[simp, reassoc]
theorem pullbackFstιToV_snd (i j : 𝒰.J) :
    pullbackFstιToV 𝒰 f g i j ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp [pullbackFstιToV, p1]

/-- We show that the map `W ×[X] Uᵢ ⟶ Uᵢ ×[Z] Y ⟶ W` is the first projection, where the
first map is given by the lift of `W ×[X] Uᵢ ⟶ Uᵢ` and `W ×[X] Uᵢ ⟶ W ⟶ Y`.

It suffices to show that the two map agrees when restricted onto `Uⱼ ×[Z] Y`. In this case,
both maps factor through `V j i` via `pullback_fst_ι_to_V` -/
theorem lift_comp_ι (i : 𝒰.J) :
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ p2 𝒰 f g)
          (by rw [← pullback.condition_assoc, Category.assoc, p_comm]) ≫
        (gluing 𝒰 f g).ι i =
      (pullback.fst _ _ : pullback (p1 𝒰 f g) (𝒰.map i) ⟶ _) := by
  apply ((gluing 𝒰 f g).openCover.pullbackCover (pullback.fst _ _)).hom_ext
  intro j
  dsimp only [OpenCover.pullbackCover]
  trans pullbackFstιToV 𝒰 f g i j ≫ fV 𝒰 f g j i ≫ (gluing 𝒰 f g).ι _
  · rw [← show _ = fV 𝒰 f g j i ≫ _ from (gluing 𝒰 f g).glue_condition j i]
    simp_rw [← Category.assoc]
    congr 1
    rw [gluing_f, gluing_t]
    apply pullback.hom_ext <;> simp_rw [Category.assoc]
    · simp_rw [t_fst_fst, pullback.lift_fst, pullbackFstιToV_snd, GlueData.openCover_map]
    · simp_rw [t_fst_snd, pullback.lift_snd, pullbackFstιToV_fst_assoc, pullback.condition_assoc,
        GlueData.openCover_map, p2]
      simp
  · rw [pullback.condition, ← Category.assoc]
    simp_rw [pullbackFstιToV_fst, GlueData.openCover_map]

/-- The canonical isomorphism between `W ×[X] Uᵢ` and `Uᵢ ×[X] Y`. That is, the preimage of `Uᵢ` in
`W` along `p1` is indeed `Uᵢ ×[X] Y`. -/
def pullbackP1Iso (i : 𝒰.J) : pullback (p1 𝒰 f g) (𝒰.map i) ≅ pullback (𝒰.map i ≫ f) g := by
  fconstructor
  · exact
      pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ p2 𝒰 f g)
        (by rw [← pullback.condition_assoc, Category.assoc, p_comm])
  · apply pullback.lift ((gluing 𝒰 f g).ι i) (pullback.fst _ _)
    rw [gluing_ι, p1, Multicoequalizer.π_desc]
  · apply pullback.hom_ext
    · simpa using lift_comp_ι 𝒰 f g i
    · simp_rw [Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp]
  · apply pullback.hom_ext
    · simp_rw [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · simp [p2]

@[simp, reassoc]
theorem pullbackP1Iso_hom_fst (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.fst _ _ = pullback.snd _ _ := by
  simp_rw [pullbackP1Iso, pullback.lift_fst]

@[simp, reassoc]
theorem pullbackP1Iso_hom_snd (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.snd _ _ = pullback.fst _ _ ≫ p2 𝒰 f g := by
  simp_rw [pullbackP1Iso, pullback.lift_snd]

@[simp, reassoc]
theorem pullbackP1Iso_inv_fst (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.fst _ _ = (gluing 𝒰 f g).ι i := by
  simp_rw [pullbackP1Iso, pullback.lift_fst]

@[simp, reassoc]
theorem pullbackP1Iso_inv_snd (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.snd _ _ = pullback.fst _ _ := by
  simp_rw [pullbackP1Iso, pullback.lift_snd]

@[simp, reassoc]
theorem pullbackP1Iso_hom_ι (i : 𝒰.J) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ Multicoequalizer.π (gluing 𝒰 f g).diagram i =
    pullback.fst _ _ := by
  rw [← gluing_ι, ← pullbackP1Iso_inv_fst, Iso.hom_inv_id_assoc]

/-- The glued scheme (`(gluing 𝒰 f g).glued`) is indeed the pullback of `f` and `g`. -/
def gluedIsLimit : IsLimit (PullbackCone.mk _ _ (p_comm 𝒰 f g)) := by
  apply PullbackCone.isLimitAux'
  intro s
  refine ⟨gluedLift 𝒰 f g s, gluedLift_p1 𝒰 f g s, gluedLift_p2 𝒰 f g s, ?_⟩
  intro m h₁ h₂
  simp_rw [PullbackCone.mk_pt, PullbackCone.mk_π_app] at h₁ h₂
  apply (𝒰.pullbackCover s.fst).hom_ext
  intro i
  rw [gluedLift, (𝒰.pullbackCover s.fst).ι_glueMorphisms, 𝒰.pullbackCover_map]
  rw [← cancel_epi
    (pullbackRightPullbackFstIso (p1 𝒰 f g) (𝒰.map i) m ≪≫ pullback.congrHom h₁ rfl).hom,
    Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
    Category.comp_id, pullbackRightPullbackFstIso_hom_fst_assoc, pullback.condition]
  conv_lhs => rhs; rw [← pullbackP1Iso_hom_ι]
  simp_rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp_rw [Category.assoc, pullbackP1Iso_hom_fst, pullback.lift_fst, Category.comp_id,
      pullbackSymmetry_hom_comp_fst, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd]
  · simp_rw [Category.assoc, pullbackP1Iso_hom_snd, pullback.lift_snd,
      pullbackSymmetry_hom_comp_snd_assoc, pullback.lift_fst_assoc, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst_assoc, ← pullback.condition_assoc, h₂]

theorem hasPullback_of_cover : HasPullback f g :=
  ⟨⟨⟨_, gluedIsLimit 𝒰 f g⟩⟩⟩

instance affine_hasPullback {A B C : CommRingCat}
    (f : Spec A ⟶ Spec C)
    (g : Spec B ⟶ Spec C) : HasPullback f g := by
  rw [← Scheme.Spec.map_preimage f, ← Scheme.Spec.map_preimage g]
  exact ⟨⟨⟨_, isLimitOfHasPullbackOfPreservesLimit
    Scheme.Spec (Scheme.Spec.preimage f) (Scheme.Spec.preimage g)⟩⟩⟩

theorem affine_affine_hasPullback {B C : CommRingCat} {X : Scheme}
    (f : X ⟶ Spec C) (g : Spec B ⟶ Spec C) :
    HasPullback f g :=
  hasPullback_of_cover X.affineCover f g

instance base_affine_hasPullback {C : CommRingCat} {X Y : Scheme} (f : X ⟶ Spec C)
    (g : Y ⟶ Spec C) : HasPullback f g :=
  @hasPullback_symmetry _ _ _ _ _ _ _
    (@hasPullback_of_cover _ _ _ Y.affineCover g f fun _ =>
      @hasPullback_symmetry _ _ _ _ _ _ _ <| affine_affine_hasPullback _ _)

instance left_affine_comp_pullback_hasPullback {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    (i : Z.affineCover.J) : HasPullback ((Z.affineCover.pullbackCover f).map i ≫ f) g := by
  simp only [OpenCover.pullbackCover_obj, OpenCover.pullbackCover_map, pullback.condition]
  exact hasPullback_assoc_symm f (Z.affineCover.map i) (Z.affineCover.map i) g

instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  hasPullback_of_cover (Z.affineCover.pullbackCover f) f g

instance : HasPullbacks Scheme :=
  hasPullbacks_of_hasLimit_cospan _

instance isAffine_of_isAffine_isAffine_isAffine {X Y Z : Scheme}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsAffine X] [IsAffine Y] [IsAffine Z] :
    IsAffine (pullback f g) :=
  isAffine_of_isIso
    (pullback.map f g (Spec.map (Γ.map f.op)) (Spec.map (Γ.map g.op))
        (ΓSpec.adjunction.unit.app X) (ΓSpec.adjunction.unit.app Y) (ΓSpec.adjunction.unit.app Z)
        (ΓSpec.adjunction.unit.naturality f) (ΓSpec.adjunction.unit.naturality g) ≫
      (PreservesPullback.iso Scheme.Spec _ _).inv)

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
  simp_rw [OpenCover.pushforwardIso_J, OpenCover.pushforwardIso_map, GlueData.openCover_map,
    GlueData.openCover_J, gluing_J]
  exact pullback.hom_ext (by simp [p1]) (by simp [p2])

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

/-- (Implementation). Use `openCoverOfBase` instead. -/
@[simps! map]
def openCoverOfBase' (𝒰 : OpenCover Z) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover (pullback f g) := by
  apply (openCoverOfLeft (𝒰.pullbackCover f) f g).bind
  intro i
  have := PullbackCone.flipIsLimit <|
    pasteVertIsPullback rfl (pullbackIsPullback g (𝒰.map i))
      (pullbackIsPullback (pullback.snd g (𝒰.map i)) (pullback.snd f (𝒰.map i)))
  refine
    @openCoverOfIsIso
      (f := (pullbackSymmetry _ _).hom ≫ (limit.isoLimitCone ⟨_, this⟩).inv ≫
        pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) ?_ ?_) inferInstance
  · simp [← pullback.condition]
  · simp only [Category.comp_id, Category.id_comp]

/-- Given an open cover `{ Zᵢ }` of `Z`, then `X ×[Z] Y` is covered by `Xᵢ ×[Zᵢ] Yᵢ`, where
  `Xᵢ = X ×[Z] Zᵢ` and `Yᵢ = Y ×[Z] Zᵢ` is the preimage of `Zᵢ` in `X` and `Y`. -/
@[simps! J obj map]
def openCoverOfBase (𝒰 : OpenCover Z) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover (pullback f g) := by
  apply
    (openCoverOfBase'.{u, u} 𝒰 f g).copy 𝒰.J
      (fun i =>
        pullback (pullback.snd _ _ : pullback f (𝒰.map i) ⟶ _)
          (pullback.snd _ _ : pullback g (𝒰.map i) ⟶ _))
      (fun i =>
        pullback.map _ _ _ _ (pullback.fst _ _) (pullback.fst _ _) (𝒰.map i)
          pullback.condition.symm pullback.condition.symm)
      ((Equiv.prodPUnit 𝒰.J).symm.trans (Equiv.sigmaEquivProd 𝒰.J PUnit).symm) fun _ => Iso.refl _
  intro i
  rw [Iso.refl_hom, Category.id_comp, openCoverOfBase'_map]
  apply pullback.hom_ext <;> dsimp <;>
  · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.assoc,
      limit.lift_π_assoc, cospan_left, Category.comp_id, limit.isoLimitCone_inv_π,
      limit.isoLimitCone_inv_π_assoc, PullbackCone.flip_pt, PullbackCone.π_app_left,
      PullbackCone.π_app_right, PullbackCone.flip_fst, PullbackCone.flip_snd,
      pullbackSymmetry_hom_comp_snd_assoc, pullbackSymmetry_hom_comp_fst_assoc]
    rfl

end Pullback

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

instance Scheme.pullback_map_isOpenImmersion {X Y S X' Y' S' : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [IsOpenImmersion i₁] [IsOpenImmersion i₂] [Mono i₃] :
    IsOpenImmersion (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) := by
  rw [pullback_map_eq_pullbackFstFstIso_inv]
  infer_instance

section Spec

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

open TensorProduct Algebra.TensorProduct CommRingCat RingHomClass

/-- The isomorphism between the fiber product of two schemes `Spec S` and `Spec T`
over a scheme `Spec R` and the `Spec` of the tensor product `S ⊗[R] T`.-/
noncomputable
def pullbackSpecIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅ Spec (.of <| S ⊗[R] T) :=
  letI H := IsLimit.equivIsoLimit (PullbackCone.eta _)
    (PushoutCocone.isColimitEquivIsLimitOp _ (CommRingCat.pushoutCoconeIsColimit R S T))
  limit.isoLimitCone ⟨_, isLimitPullbackConeMapOfIsLimit Scheme.Spec _ H⟩
/--
The composition of the inverse of the isomorphism `pullbackSepcIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the first projection is
the morphism `Spec (S ⊗[R] T) ⟶ Spec S` obtained by applying `Spec.map` to the ring morphism
`s ↦ s ⊗ₜ[R] 1`.
-/
@[reassoc (attr := simp)]
lemma pullbackSpecIso_inv_fst :
    (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ = Spec.map (ofHom includeLeftRingHom) :=
  limit.isoLimitCone_inv_π _ _
/--
The composition of the inverse of the isomorphism `pullbackSepcIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the second projection is
the morphism `Spec (S ⊗[R] T) ⟶ Spec T` obtained by applying `Spec.map` to the ring morphism
`t ↦ 1 ⊗ₜ[R] t`.
-/
@[reassoc (attr := simp)]
lemma pullbackSpecIso_inv_snd :
    (pullbackSpecIso R S T).inv ≫ pullback.snd _ _ = Spec.map (ofHom (toRingHom includeRight)) :=
  limit.isoLimitCone_inv_π _ _
/--
The composition of the isomorphism `pullbackSepcIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the morphism
`Spec (S ⊗[R] T) ⟶ Spec S` obtained by applying `Spec.map` to the ring morphism `s ↦ s ⊗ₜ[R] 1`
is the first projection.
-/
@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_fst :
    (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom includeLeftRingHom) = pullback.fst _ _ := by
  rw [← pullbackSpecIso_inv_fst, Iso.hom_inv_id_assoc]
/--
The composition of the isomorphism `pullbackSepcIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the morphism
`Spec (S ⊗[R] T) ⟶ Spec T` obtained by applying `Spec.map` to the ring morphism `t ↦ 1 ⊗ₜ[R] t`
is the second projection.
-/
@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_snd :
    (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom (toRingHom includeRight)) = pullback.snd _ _ := by
  rw [← pullbackSpecIso_inv_snd, Iso.hom_inv_id_assoc]

end Spec


end AlgebraicGeometry
