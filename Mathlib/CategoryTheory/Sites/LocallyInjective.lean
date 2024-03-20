/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Locally injective morphisms of (pre)sheaves

Let `C` be a category equipped with a Grothendieck topology `J`,
and let `D` be a concrete category.

In this file, we introduce the typeclasses `Presheaf.LocallyInjective J φ`
for a morphism `φ : F₁ ⟶ F₂` in the category `Cᵒᵖ ⥤ D`. This means that `φ` is locally
injective. More precisely, if `x` and `y` are two elements of some `F₁.obj U` such
the images of `x` and `y` in `F₂.obj U` coincide, then the sieve
`Presheaf.equalizerSieve x y` must be a covering sieve.

-/

universe w v' v u' u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] [ConcreteCategory.{w} D]
  (J : GrothendieckTopology C)

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

namespace Presheaf

/-- If `F : Cᵒᵖ ⥤ D` is a presheaf with values in a concrete category, if `x` and `y` are
elements in `F.obj X`, this is the sieve of `X.unop` consisting of morphisms `f`
such that `F.map f.op x = F.map f.op y`. -/
@[simps]
def equalizerSieve {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : F.obj X) : Sieve X.unop where
  arrows _ f := F.map f.op x = F.map f.op y
  downward_closed {X Y} f hf g := by
    dsimp at hf ⊢
    simp [hf]

variable {F₁ F₂ F₃ : Cᵒᵖ ⥤ D} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)

/-- A morphism `φ : F₁ ⟶ F₂` of presheaves `Cᵒᵖ ⥤ D` (with `D` a concrete category)
is locally injective for a Grothendieck topology `J` on `C` if
whenever two sections of `F₁` are sent to the same section of `F₂`, then these two
sections coincide locally. -/
class IsLocallyInjective : Prop where
  equalizerSieve_mem {X : Cᵒᵖ} (x y : F₁.obj X) (h : φ.app X x = φ.app X y) :
    equalizerSieve x y ∈ J X.unop

lemma equalizerSieve_mem [IsLocallyInjective J φ]
    {X : Cᵒᵖ} (x y : F₁.obj X) (h : φ.app X x = φ.app X y) :
    equalizerSieve x y ∈ J X.unop :=
  IsLocallyInjective.equalizerSieve_mem x y h

lemma isLocallyInjective_of_injective (hφ : ∀ (X : Cᵒᵖ), Function.Injective (φ.app X)) :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y h := by
    convert J.top_mem X.unop
    ext Y f
    simp only [equalizerSieve_apply, op_unop, Sieve.top_apply, iff_true]
    apply hφ
    simp [h]

instance [IsIso φ] :
    IsLocallyInjective J φ := isLocallyInjective_of_injective J φ (fun X => by
  apply Function.Bijective.injective
  rw [← isIso_iff_bijective]
  change IsIso ((forget D).map (φ.app X))
  infer_instance)

instance isLocallyInjective_forget [IsLocallyInjective J φ] :
    IsLocallyInjective J (whiskerRight φ (forget D)) where
  equalizerSieve_mem x y h := equalizerSieve_mem J φ x y h

instance isLocallyInjective_comp [IsLocallyInjective J φ] [IsLocallyInjective J ψ] :
    IsLocallyInjective J (φ ≫ ψ) where
  equalizerSieve_mem {X} x y h := by
    let S := equalizerSieve (φ.app _ x) (φ.app _ y)
    let T : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X.unop⦄ (_ : S f), Sieve Y := fun Y f _ =>
      equalizerSieve (F₁.map f.op x) ((F₁.map f.op y))
    refine J.superset_covering ?_
      (J.transitive (equalizerSieve_mem J ψ (φ.app _ x) (φ.app _ y) (by simpa using h))
      (Sieve.bind S.1 T) ?_)
    · rintro Y f ⟨Z, a, g, hg, ha, rfl⟩
      simpa using ha
    · intro U f hf
      exact J.superset_covering (Sieve.le_pullback_bind S.1 T _ hf)
        (equalizerSieve_mem J φ (F₁.map f.op x) (F₁.map f.op y) (by simpa using hf))

lemma isLocallyInjective_of_isLocallyInjective [IsLocallyInjective J (φ ≫ ψ)] :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y h := equalizerSieve_mem J (φ ≫ ψ) x y (by simp [h])

variable {φ ψ}

lemma isLocallyInjective_of_isLocallyInjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
    [IsLocallyInjective J φψ] : IsLocallyInjective J φ := by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective J φ ψ

lemma isLocallyInjective_iff_of_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [IsLocallyInjective J ψ] :
    IsLocallyInjective J φψ ↔ IsLocallyInjective J φ := by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

variable (φ ψ)

lemma isLocallyInjective_comp_iff [IsLocallyInjective J ψ] :
    IsLocallyInjective J (φ ≫ ψ) ↔ IsLocallyInjective J φ :=
  isLocallyInjective_iff_of_fac J rfl

variable (F₁) in
/-- Condition that a presheaf with values in a concrete category is separated for
a Grothendieck topology. -/
def IsSeparated : Prop :=
  ∀ (X : C) (S : Sieve X) (_ : S ∈ J X) (x y : F₁.obj (op X)),
    (∀ (Y : C) (f : Y ⟶ X) (_ : S f), F₁.map f.op x = F₁.map f.op y) → x = y

lemma isLocallyInjective_iff_injective_of_separated (hsep : IsSeparated J F₁) :
    IsLocallyInjective J φ ↔ ∀ (X : Cᵒᵖ), Function.Injective (φ.app X) := by
  constructor
  · intro _ X x y h
    exact hsep X.unop _ (equalizerSieve_mem J φ x y h) _ _ (fun _ _ hf => hf)
  · apply isLocallyInjective_of_injective

instance (F : Cᵒᵖ ⥤ Type w) (G : GrothendieckTopology.Subpresheaf F) :
    IsLocallyInjective J G.ι :=
  isLocallyInjective_of_injective _ _ (fun X => by
    intro ⟨x, _⟩ ⟨y, _⟩ h
    exact Subtype.ext h)

section

variable {E : Type u'} [Category.{max u v} E] [ConcreteCategory E]
  [PreservesLimits (forget E)]
  [∀ (P : Cᵒᵖ ⥤ E) (X : C) (S : J.Cover X),
    HasMultiequalizer (GrothendieckTopology.Cover.index S P)]
  [∀ (X : C), HasColimitsOfShape (GrothendieckTopology.Cover J X)ᵒᵖ E]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget E)] [ReflectsIsomorphisms (forget E)]

variable (P : Cᵒᵖ ⥤ E)

open GrothendieckTopology Plus

instance isLocallyInjective_toPlus : IsLocallyInjective J (J.toPlus P) where
  equalizerSieve_mem {X} x y h := by
    erw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

instance isLocallyInjective_toSheafify : IsLocallyInjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

instance isLocallyInjective_toSheafify' : IsLocallyInjective J (toSheafify J P) := by
  rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

end

end Presheaf

namespace Sheaf

variable {J}
variable {F₁ F₂ : Sheaf J D} (φ : F₁ ⟶ F₂)

/-- If `φ : F₁ ⟶ F₂` is a morphism of sheaves, this is an abbreviation for
`Presheaf.IsLocallyInjective J φ.val`. Under suitable assumptions, it
is equivalent to the injectivity of all maps `φ.val.app X`,
see `isLocallyInjective_iff_injective`. -/
abbrev IsLocallyInjective := Presheaf.IsLocallyInjective J φ.val

variable [J.HasSheafCompose (forget D)]

instance isLocallyInjective_forget [IsLocallyInjective φ] :
    IsLocallyInjective ((sheafCompose J (forget D)).map φ) :=
  Presheaf.isLocallyInjective_forget J φ.1

variable (F₁) in
lemma isSeparated : Presheaf.IsSeparated J F₁.val := by
  rintro X S hS x y h
  exact (Presieve.isSeparated_of_isSheaf _ _ ((isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose J (forget D)).obj F₁).2) S hS).ext (fun _ _ hf => h _ _ hf)

lemma isLocallyInjective_iff_injective :
    IsLocallyInjective φ ↔ ∀ (X : Cᵒᵖ), Function.Injective (φ.val.app X) :=
  Presheaf.isLocallyInjective_iff_injective_of_separated _ _ F₁.isSeparated

instance {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallyInjective (GrothendieckTopology.imageSheafι f) := by
  dsimp [GrothendieckTopology.imageSheafι]
  infer_instance

end Sheaf

end CategoryTheory
