/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
# The diagonal object of a morphism.

We provide various API and isomorphisms considering the diagonal object `Δ_{Y/X} := pullback f f`
of a morphism `f : X ⟶ Y`.

-/

@[expose] public section


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {X Y Z : C}

namespace pullback

section Diagonal

variable (f : X ⟶ Y) [HasPullback f f]

/-- The diagonal object of a morphism `f : X ⟶ Y` is `Δ_{X/Y} := pullback f f`. -/
abbrev diagonalObj : C :=
  pullback f f

/-- The diagonal morphism `X ⟶ Δ_{X/Y}` for a morphism `f : X ⟶ Y`. -/
def diagonal : X ⟶ diagonalObj f :=
  pullback.lift (𝟙 _) (𝟙 _) rfl

@[reassoc (attr := simp)]
theorem diagonal_fst : diagonal f ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem diagonal_snd : diagonal f ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

instance : IsSplitMono (diagonal f) :=
  ⟨⟨⟨pullback.fst _ _, diagonal_fst f⟩⟩⟩

instance : IsSplitEpi (pullback.fst f f) :=
  ⟨⟨⟨diagonal f, diagonal_fst f⟩⟩⟩

instance : IsSplitEpi (pullback.snd f f) :=
  ⟨⟨⟨diagonal f, diagonal_snd f⟩⟩⟩

instance [Mono f] : IsIso (diagonal f) := by
  rw [(IsIso.inv_eq_of_inv_hom_id (diagonal_fst f)).symm]
  infer_instance

lemma isIso_diagonal_iff : IsIso (diagonal f) ↔ Mono f :=
  ⟨fun H ↦ ⟨fun _ _ e ↦ by rw [← lift_fst _ _ e, (cancel_epi (g := fst f f) (h := snd f f)
    (diagonal f)).mp (by simp), lift_snd]⟩, fun _ ↦ inferInstance⟩

/-- The two projections `Δ_{X/Y} ⟶ X` form a kernel pair for `f : X ⟶ Y`. -/
theorem diagonal_isKernelPair : IsKernelPair f (pullback.fst f f) (pullback.snd f f) :=
  IsPullback.of_hasPullback f f

end Diagonal

end pullback

section Diagonal

variable [HasPullbacks C]

open pullback

section

variable {U V₁ V₂ : C} (f : X ⟶ Y) (i : U ⟶ Y)
variable (i₁ : V₁ ⟶ pullback f i) (i₂ : V₂ ⟶ pullback f i)

@[reassoc (attr := simp)]
theorem pullback_diagonal_map_snd_fst_fst :
    (pullback.snd (diagonal f)
      (map (i₁ ≫ snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i
        (by simp [condition]) (by simp [condition]))) ≫
      fst _ _ ≫ i₁ ≫ fst _ _ =
      pullback.fst _ _ := by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_fst f, pullback.condition_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem pullback_diagonal_map_snd_snd_fst :
    (pullback.snd (diagonal f)
      (map (i₁ ≫ snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i
        (by simp [condition]) (by simp [condition]))) ≫
      snd _ _ ≫ i₂ ≫ fst _ _ =
      pullback.fst _ _ := by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_snd f, pullback.condition_assoc, pullback.lift_snd]

variable [HasPullback i₁ i₂]

/-- The underlying map of `pullbackDiagonalIso` -/
abbrev pullbackDiagonalMapIso.hom :
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) ⟶
      pullback i₁ i₂ :=
  pullback.lift (pullback.snd _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
  ext
  · simp only [Category.assoc, pullback_diagonal_map_snd_fst_fst,
      pullback_diagonal_map_snd_snd_fst]
  · simp only [Category.assoc, condition])

set_option backward.isDefEq.respectTransparency false in
/-- The underlying inverse of `pullbackDiagonalIso` -/
abbrev pullbackDiagonalMapIso.inv : pullback i₁ i₂ ⟶
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) :=
    pullback.lift (pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _)
      (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.snd _ _) (Category.id_comp _).symm
        (Category.id_comp _).symm) (by
        ext
        · simp only [Category.assoc, diagonal_fst, Category.comp_id, limit.lift_π,
            PullbackCone.mk_pt, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left]
        · simp only [condition_assoc, Category.assoc, diagonal_snd, Category.comp_id, limit.lift_π,
            PullbackCone.mk_pt, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right])

set_option backward.isDefEq.respectTransparency false in
/-- This iso witnesses the fact that
given `f : X ⟶ Y`, `i : U ⟶ Y`, and `i₁ : V₁ ⟶ X ×[Y] U`, `i₂ : V₂ ⟶ X ×[Y] U`, the diagram

```
V₁ ×[X ×[Y] U] V₂ ⟶ V₁ ×[U] V₂
        |                 |
        |                 |
        ↓                 ↓
        X         ⟶   X ×[Y] X
```

is a pullback square.
Also see `pullback_fst_map_snd_isPullback`.
-/
def pullbackDiagonalMapIso :
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) ≅
      pullback i₁ i₂ where
  hom := pullbackDiagonalMapIso.hom f i i₁ i₂
  inv := pullbackDiagonalMapIso.inv f i i₁ i₂

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso.hom_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso.hom_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso.inv_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso.inv_snd_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIso.inv_snd_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  delta pullbackDiagonalMapIso
  simp

set_option backward.isDefEq.respectTransparency false in
theorem pullback_fst_map_snd_isPullback :
    IsPullback (fst _ _ ≫ i₁ ≫ fst _ _)
      (map i₁ i₂ (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) _ _ _
        (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal f)
      (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i (by simp [condition])
        (by simp [condition])) :=
  IsPullback.of_iso_pullback ⟨by ext <;> simp [condition_assoc]⟩
    (pullbackDiagonalMapIso f i i₁ i₂).symm (pullbackDiagonalMapIso.inv_fst f i i₁ i₂)
    (by cat_disch)

end

section

variable {S T : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S)
variable [HasPullback i i] [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)]
variable
  [HasPullback (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _))]

set_option backward.isDefEq.respectTransparency false in
/-- This iso witnesses the fact that
given `f : X ⟶ T`, `g : Y ⟶ T`, and `i : T ⟶ S`, the diagram

```
X ×ₜ Y ⟶ X ×ₛ Y
  |         |
  |         |
  ↓         ↓
  T    ⟶  T ×ₛ T
```

is a pullback square.
Also see `pullback_map_diagonal_isPullback`.
-/
def pullbackDiagonalMapIdIso :
    pullback (diagonal i)
        (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ≅
      pullback f g := by
  refine ?_ ≪≫
    pullbackDiagonalMapIso i (𝟙 _) (f ≫ inv (pullback.fst _ _)) (g ≫ inv (pullback.fst _ _)) ≪≫ ?_
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 T) ((pullback.congrHom ?_ ?_).hom) (𝟙 _) ?_ ?_)
      ?_
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
    · rw [Category.comp_id, Category.id_comp]
    · ext <;> simp
    · infer_instance
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.fst _ _) ?_ ?_) ?_
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · infer_instance

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_hom_fst :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIdIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_hom_snd :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta pullbackDiagonalMapIdIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_inv_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f := by
  rw [Iso.inv_comp_eq, ← Category.comp_id (pullback.fst _ _), ← diagonal_fst i,
    pullback.condition_assoc]
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_inv_snd_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  rw [Iso.inv_comp_eq]
  simp

@[reassoc (attr := simp)]
theorem pullbackDiagonalMapIdIso_inv_snd_snd :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  rw [Iso.inv_comp_eq]
  simp

theorem pullback.diagonal_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    diagonal (f ≫ g) = diagonal f ≫ (pullbackDiagonalMapIdIso f f g).inv ≫ pullback.snd _ _ := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pullback.comp_diagonal (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ pullback.diagonal g = pullback.diagonal (f ≫ g) ≫
      pullback.map (f ≫ g) (f ≫ g) g g f f (𝟙 Z) (by simp) (by simp) := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem pullback_map_diagonal_isPullback :
    IsPullback (pullback.fst _ _ ≫ f)
      (pullback.map f g (f ≫ i) (g ≫ i) _ _ i (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
  apply IsPullback.of_iso_pullback _ (pullbackDiagonalMapIdIso f g i).symm
  · simp
  · ext <;> simp
  · constructor
    ext <;> simp [condition]

/-- The diagonal object of `X ×[Z] Y ⟶ X` is isomorphic to `Δ_{Y/Z} ×[Z] X`. -/
def diagonalObjPullbackFstIso {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonalObj (pullback.fst f g) ≅
      pullback (pullback.snd _ _ ≫ g : diagonalObj g ⟶ Z) f :=
  pullbackRightPullbackFstIso _ _ _ ≪≫
    pullback.congrHom pullback.condition rfl ≪≫
      pullbackAssoc _ _ _ _ ≪≫ pullbackSymmetry _ _ ≪≫ pullback.congrHom pullback.condition rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_hom_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_hom_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_hom_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_snd_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem diagonalObjPullbackFstIso_inv_snd_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
theorem diagonal_pullback_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonal (pullback.fst f g) =
      (pullbackSymmetry _ _).hom ≫
        ((Over.pullback f).map
              (Over.homMk (diagonal g) : Over.mk g ⟶ Over.mk (pullback.snd _ _ ≫ g))).left ≫
          (diagonalObjPullbackFstIso f g).inv := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Informally, this is a special case of `pullback_map_diagonal_isPullback` for `T = X`. -/
lemma pullback_lift_diagonal_isPullback (g : Y ⟶ X) (f : X ⟶ S) :
    IsPullback g (pullback.lift (𝟙 Y) g (by simp)) (diagonal f)
      (pullback.map (g ≫ f) f f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) := by
  let i : pullback (g ≫ f) f ≅ pullback (g ≫ f) (𝟙 X ≫ f) := congrHom rfl (by simp)
  let e : pullback (diagonal f) (map (g ≫ f) f f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) ≅
      pullback (diagonal f) (map (g ≫ f) (𝟙 X ≫ f) f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) :=
    (asIso (map _ _ _ _ (𝟙 _) i.inv (𝟙 _) (by simp) (by ext <;> simp [i]))).symm
  apply IsPullback.of_iso_pullback _
      (e ≪≫ pullbackDiagonalMapIdIso (T := X) (S := S) g (𝟙 X) f ≪≫ asIso (pullback.fst _ _)).symm
  · simp [e]
  · ext <;> simp [e, i]
  · constructor
    ext <;> simp

end

set_option backward.isDefEq.respectTransparency false in
/-- Given the following diagram with `S ⟶ S'` a monomorphism,

```
    X ⟶ X'
      ↘      ↘
        S ⟶ S'
      ↗      ↗
    Y ⟶ Y'
```

This iso witnesses the fact that

```
      X ×[S] Y ⟶ (X' ×[S'] Y') ×[Y'] Y
          |                  |
          |                  |
          ↓                  ↓
(X' ×[S'] Y') ×[X'] X ⟶ X' ×[S'] Y'
```

is a pullback square. The diagonal map of this square is `pullback.map`.
Also see `pullback_lift_map_is_pullback`.
-/
@[simps]
def pullbackFstFstIso {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [Mono i₃] :
    pullback (pullback.fst _ _ : pullback (pullback.fst _ _ : pullback f' g' ⟶ _) i₁ ⟶ _)
        (pullback.fst _ _ : pullback (pullback.snd _ _ : pullback f' g' ⟶ _) i₂ ⟶ _) ≅
      pullback f g where
  hom :=
    pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by
        rw [← cancel_mono i₃, Category.assoc, Category.assoc, Category.assoc, Category.assoc, e₁,
          e₂, ← pullback.condition_assoc, pullback.condition_assoc, pullback.condition,
          pullback.condition_assoc])
  inv :=
    pullback.lift
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) (pullback.fst _ _) (pullback.lift_fst ..))
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) (pullback.snd _ _) (pullback.lift_snd ..))
      (by rw [pullback.lift_fst, pullback.lift_fst])
  hom_inv_id := by
    -- We could use `ext` here to immediately descend to the leaf goals,
    -- but it only obscures the structure.
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, lift_fst, lift_fst_assoc, Category.id_comp]
          rw [condition]
        · simp [Category.assoc, condition]
      · simp only [Category.assoc, lift_snd, lift_fst, Category.id_comp]
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, lift_fst, Category.id_comp]
          rw [← condition_assoc, condition]
        · simp only [Category.assoc, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.id_comp]
          rw [condition]
      · simp only [Category.assoc, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, lift_snd, Category.id_comp]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, Category.id_comp]

theorem pullback_map_eq_pullbackFstFstIso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ =
      (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ := by
  simp only [pullbackFstFstIso_inv, lift_snd_assoc, lift_fst]

set_option backward.isDefEq.respectTransparency false in
theorem pullback_lift_map_isPullback {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
    (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    IsPullback (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (fst _ _) (lift_fst _ _ _))
      (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (snd _ _) (lift_snd _ _ _))
      (pullback.fst _ _) (pullback.fst _ _) :=
  IsPullback.of_iso_pullback ⟨by rw [lift_fst, lift_fst]⟩
    (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).symm (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
lemma isPullback_map_snd_snd {X Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    IsPullback (pullback.map _ _ _ _ (pullback.snd f g) (pullback.snd f h) f
        pullback.condition pullback.condition)
      (pullback.fst (pullback.fst f g) (pullback.fst f h))
      (pullback.fst g h) (pullback.snd f g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd
        (pullback.lift (c.snd ≫ pullback.fst _ _) (c.fst ≫ pullback.snd _ _) ?_) ?_
    · simp [pullback.condition, ← c.condition_assoc]
    · simp
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    apply pullback.hom_ext <;> simp
  · intro c m hfst hsnd
    refine pullback.hom_ext (by simpa) ?_
    apply pullback.hom_ext <;> simp [← hsnd, pullback.condition, ← hfst]

end Diagonal

section Codiagonal

namespace pushout

variable {X Y : C} (f : X ⟶ Y) [HasPushout f f]

/-- The codiagonal object of a morphism `f : X ⟶ Y` is `pushout f f`. -/
noncomputable abbrev codiagonalObj (f : X ⟶ Y) [HasPushout f f] : C :=
  pushout f f

/-- The codiagonal morphism `pushout f f ⟶ Y` for a morphism `f : X ⟶ Y`. -/
noncomputable def codiagonal (f : X ⟶ Y) [HasPushout f f] : codiagonalObj f ⟶ Y :=
  pushout.desc (𝟙 Y) (𝟙 Y) rfl

@[reassoc (attr := simp)]
theorem inl_codiagonal : pushout.inl _ _ ≫ codiagonal f = 𝟙 _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_codiagonal : pushout.inr _ _ ≫ codiagonal f = 𝟙 _ :=
  pushout.inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma op_codiagonal :
    (pushout.codiagonal f).op = pullback.diagonal f.op ≫ (pullbackIsoOpPushout _ _).hom := by
  rw [← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

instance : IsSplitEpi (codiagonal f) :=
  ⟨⟨⟨pushout.inl _ _, inl_codiagonal f⟩⟩⟩

instance : IsSplitMono (pushout.inl f f) :=
  ⟨⟨⟨codiagonal f, inl_codiagonal f⟩⟩⟩

instance : IsSplitMono (pushout.inr f f) :=
  ⟨⟨⟨codiagonal f, inr_codiagonal f⟩⟩⟩

instance [Epi f] : IsIso (codiagonal f) := by
  rw [(IsIso.inv_eq_of_hom_inv_id (inl_codiagonal f)).symm]
  infer_instance

lemma isIso_codiagonal_iff : IsIso (codiagonal f) ↔ Epi f :=
  ⟨fun H ↦ ⟨fun _ _ e ↦ by rw [← inl_desc _ _ e, (cancel_mono (g := inl f f) (h := inr f f)
    (codiagonal f)).mp (by simp), inr_desc]⟩, fun _ ↦ inferInstance⟩

end pushout

variable [HasPushouts C]

set_option backward.isDefEq.respectTransparency false in
/--
Given `f : T ⟶ X`, `g : T ⟶ Y`, and `i : S ⟶ T`, the diagram
```
X ⨿ₛ Y ⟶ X ⨿ₜ Y
  ↑        ↑
  |        |
  |        |
T ⨿ₛ T  ⟶  T
```
is a pushout square.
-/
theorem isPushout_map_codiagonal {S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) :
    IsPushout
      (pushout.map i i (i ≫ f) (i ≫ g) f g (𝟙 _) (by simp) (by simp))
      (pushout.codiagonal i)
      (pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (by simp) (by simp))
      (f ≫ pushout.inl _ _) := by
  rw [← IsPullback.op_iff]
  simp only [op_pushoutMap, Quiver.Hom.unop_op, op_comp, unop_comp, op_id, pushout.op_codiagonal]
  exact .of_iso (pullback_map_diagonal_isPullback f.op g.op i.op)
    (pullbackIsoOpPushout _ _) (.refl _) (pullbackIsoOpPushout _ _) (pullbackIsoOpPushout _ _)
    (by simp [← Iso.inv_comp_eq]) (by simp) (by simp) (by simp)

end Codiagonal

end CategoryTheory.Limits
