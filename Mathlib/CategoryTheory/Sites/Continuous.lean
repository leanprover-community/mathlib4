/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.Hypercover.IsSheaf

/-!
# Continuous functors between sites.

We define the notion of continuous functor between sites: these are functors `F` such that
the precomposition with `F.op` preserves sheaves of types (and actually sheaves in any
category).

## Main definitions

* `Functor.IsContinuous`: a functor between sites is continuous if the
  precomposition with this functor preserves sheaves with values in
  the category `Type t` for a certain auxiliary universe `t`.
* `Functor.sheafPushforwardContinuous`: the induced functor
  `Sheaf K A ⥤ Sheaf J A` for a continuous functor `G : (C, J) ⥤ (D, K)`. In case this is
  part of a morphism of sites, this would be understood as the pushforward functor
  even though it goes in the opposite direction as the functor `G`. (Here, the auxiliary
  universe `t` in the assumption that `G` is continuous is the one such that morphisms
  in the category `A` are in `Type t`.)
* `Functor.PreservesOneHypercovers`: a type-class expressing that a functor preserves
  1-hypercovers of a certain size

## Main result

- `Functor.isContinuous_of_preservesOneHypercovers`: if the topology on `C` is generated
  by 1-hypercovers of size `w` and that `F : C ⥤ D` preserves 1-hypercovers of size `w`,
  then `F` is continuous (for any auxiliary universe parameter `t`).
  This is an instance for `w = max u₁ v₁` when `C : Type u₁` and `[Category.{v₁} C]`

## References
* https://stacks.math.columbia.edu/tag/00WU

-/

universe w t v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

namespace PreOneHypercover

variable {X : C} (E : PreOneHypercover X) (F : C ⥤ D)

/-- The image of a 1-pre-hypercover by a functor. -/
@[simps]
def map : PreOneHypercover (F.obj X) where
  I₀ := E.I₀
  X i := F.obj (E.X i)
  f i := F.map (E.f i)
  I₁ := E.I₁
  Y _ _ j := F.obj (E.Y j)
  p₁ _ _ j := F.map (E.p₁ j)
  p₂ _ _ j := F.map (E.p₂ j)
  w _ _ j := by simpa using F.congr_map (E.w j)

/-- If `F : C ⥤ D`, `P : Dᵒᵖ ⥤ A` and `E` is a 1-pre-hypercover of an object of `X`,
then `(E.map F).multifork P` is a limit iff `E.multifork (F.op ⋙ P)` is a limit. -/
def isLimitMapMultiforkEquiv {A : Type u} [Category.{t} A] (P : Dᵒᵖ ⥤ A) :
    IsLimit ((E.map F).multifork P) ≃ IsLimit (E.multifork (F.op ⋙ P)) := by rfl

end PreOneHypercover

namespace GrothendieckTopology

namespace OneHypercover

variable {J : GrothendieckTopology C} {X : C} (E : J.OneHypercover X)

/-- A 1-hypercover in `C` is preserved by a functor `F : C ⥤ D` if the mapped 1-pre-hypercover
in `D` is a 1-hypercover for the given topology on `D`. -/
class IsPreservedBy (F : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  mem₀ : (E.toPreOneHypercover.map F).sieve₀ ∈ K (F.obj X)
  mem₁ (i₁ i₂ : E.I₀) ⦃W : D⦄ (p₁ : W ⟶ F.obj (E.X i₁)) (p₂ : W ⟶ F.obj (E.X i₂))
    (w : p₁ ≫ F.map (E.f i₁) = p₂ ≫ F.map (E.f i₂)) :
      (E.toPreOneHypercover.map F).sieve₁ p₁ p₂ ∈ K W

/-- Given a 1-hypercover `E : J.OneHypercover X` of an object of `C`, a functor `F : C ⥤ D`
such that `E.IsPreservedBy F K` for a Grothendieck topology `K` on `D`, this is
the image of `E` by `F`, as a 1-hypercover of `F.obj X` for `K`. -/
@[simps! toPreOneHypercover]
def map (F : C ⥤ D) (K : GrothendieckTopology D) [E.IsPreservedBy F K] :
    K.OneHypercover (F.obj X) where
  toPreOneHypercover := E.toPreOneHypercover.map F
  mem₀ := IsPreservedBy.mem₀
  mem₁ _ _ _ _ _ h := IsPreservedBy.mem₁ _ _ _ _ h

instance : E.IsPreservedBy (𝟭 C) J where
  mem₀ := E.mem₀
  mem₁ := E.mem₁

end OneHypercover

end GrothendieckTopology

namespace Functor

variable (F : C ⥤ D) {A : Type u} [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- The condition that a functor `F : C ⥤ D` sends 1-hypercovers for
`J : GrothendieckTopology C` to 1-hypercovers for `K : GrothendieckTopology D`. -/
abbrev PreservesOneHypercovers :=
  ∀ {X : C} (E : GrothendieckTopology.OneHypercover.{w} J X), E.IsPreservedBy F K

/-- A functor `F` is continuous if the precomposition with `F.op` sends sheaves of `Type t`
to sheaves. -/
class IsContinuous : Prop where
  op_comp_isSheaf_of_types (G : Sheaf K (Type t)) : Presieve.IsSheaf J (F.op ⋙ G.val)

lemma op_comp_isSheaf_of_types [Functor.IsContinuous.{t} F J K] (G : Sheaf K (Type t)) :
    Presieve.IsSheaf J (F.op ⋙ G.val) :=
  Functor.IsContinuous.op_comp_isSheaf_of_types _

lemma op_comp_isSheaf [Functor.IsContinuous.{t} F J K] (G : Sheaf K A) :
    Presheaf.IsSheaf J (F.op ⋙ G.val) :=
  fun T => F.op_comp_isSheaf_of_types J K ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (G.cond T)⟩

lemma isContinuous_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous.{t} F₁ J K] : Functor.IsContinuous.{t} F₂ J K where
  op_comp_isSheaf_of_types G :=
    Presieve.isSheaf_iso J (isoWhiskerRight (NatIso.op e.symm) _)
      (F₁.op_comp_isSheaf_of_types J K G)

instance isContinuous_id : Functor.IsContinuous.{w} (𝟭 C) J J where
  op_comp_isSheaf_of_types G := (isSheaf_iff_isSheaf_of_type _ _).1 G.2

lemma isContinuous_comp (F₁ : C ⥤ D) (F₂ : D ⥤ E) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [Functor.IsContinuous.{t} F₁ J K] [Functor.IsContinuous.{t} F₂ K L] :
    Functor.IsContinuous.{t} (F₁ ⋙ F₂) J L where
  op_comp_isSheaf_of_types G :=
    F₁.op_comp_isSheaf_of_types J K
      ⟨_,(isSheaf_iff_isSheaf_of_type _ _).2 (F₂.op_comp_isSheaf_of_types K L G)⟩

lemma isContinuous_comp' {F₁ : C ⥤ D} {F₂ : D ⥤ E} {F₁₂ : C ⥤ E}
    (e : F₁ ⋙ F₂ ≅ F₁₂) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [Functor.IsContinuous.{t} F₁ J K] [Functor.IsContinuous.{t} F₂ K L] :
    Functor.IsContinuous.{t} F₁₂ J L := by
  have := Functor.isContinuous_comp F₁ F₂ J K L
  apply Functor.isContinuous_of_iso e

section

lemma op_comp_isSheaf_of_preservesOneHypercovers
    [PreservesOneHypercovers.{w} F J K] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J]
    (P : Dᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf J (F.op ⋙ P) := by
  rw [Presheaf.isSheaf_iff_of_isGeneratedByOneHypercovers.{w}]
  intro X E
  exact ⟨(E.toPreOneHypercover.isLimitMapMultiforkEquiv F P)
    ((E.map F K).isLimitMultifork ⟨P, hP⟩)⟩

lemma isContinuous_of_preservesOneHypercovers
    [PreservesOneHypercovers.{w} F J K] [GrothendieckTopology.IsGeneratedByOneHypercovers.{w} J] :
    IsContinuous.{t} F J K where
  op_comp_isSheaf_of_types := by
    rintro ⟨P, hP⟩
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F.op_comp_isSheaf_of_preservesOneHypercovers J K P hP

end

instance [PreservesOneHypercovers.{max u₁ v₁} F J K] :
    IsContinuous.{t} F J K :=
  isContinuous_of_preservesOneHypercovers.{max u₁ v₁} F J K

variable (A)
variable [Functor.IsContinuous.{t} F J K]

/-- The induced functor `Sheaf K A ⥤ Sheaf J A` given by `F.op ⋙ _`
if `F` is a continuous functor.
-/
@[simps!]
def sheafPushforwardContinuous : Sheaf K A ⥤ Sheaf J A where
  obj ℱ := ⟨F.op ⋙ ℱ.val, F.op_comp_isSheaf J K ℱ⟩
  map f := ⟨((whiskeringLeft _ _ _).obj F.op).map f.val⟩

/-- The functor `F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A`
is induced by the precomposition with `F.op`. -/
@[simps!]
def sheafPushforwardContinuousCompSheafToPresheafIso :
    F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (whiskeringLeft _ _ _).obj F.op := Iso.refl _

end Functor

end CategoryTheory
