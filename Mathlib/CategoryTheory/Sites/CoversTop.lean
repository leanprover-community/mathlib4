/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Sheaf

/-! Objects which cover the terminal object

In this file, given a site `(C, J)`, we introduce the notion of a family
of objects `Y : I → C` which "cover the final object": this means
that for all `X : C`, the sieve `Sieve.ofObjects Y X` is covering for `J`.
When there is a terminal object `X : C`, then `J.CoversTop Y`
holds iff `Sieve.ofObjects Y X` is covering for `J`.

We introduce a notion of compatible family of elements on objects `Y`
and obtain `Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section`
which asserts that if a presheaf of types is a sheaf, then any compatible
family of elements on objects `Y` which cover the final object extends as
a section of this presheaf.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A]

namespace GrothendieckTopology

/-- A family of objects `Y : I → C` "covers the final object"
if for all `X : C`, the sieve `ofObjects Y X` is a covering sieve. -/
def CoversTop {I : Type*} (Y : I → C) : Prop :=
  ∀ (X : C), Sieve.ofObjects Y X ∈ J X

lemma coversTop_iff_of_isTerminal (X : C) (hX : IsTerminal X)
    {I : Type*} (Y : I → C) :
    J.CoversTop Y ↔ Sieve.ofObjects Y X ∈ J X := by
  constructor
  · tauto
  · intro h W
    apply J.superset_covering _ (J.pullback_stable (hX.from W) h)
    rintro T a ⟨i, ⟨b⟩⟩
    exact ⟨i, ⟨b⟩⟩

namespace CoversTop

variable {J}
variable {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
include hY

/-- The cover of any object `W : C` attached to a family of objects `Y` that satisfy
`J.CoversTop Y` -/
abbrev cover (W : C) : Cover J W := ⟨Sieve.ofObjects Y W, hY W⟩

lemma ext (F : Sheaf J A) {c : Cone F.1} (hc : IsLimit c) {X : A} {f g : X ⟶ c.pt}
    (h : ∀ (i : I), f ≫ c.π.app (Opposite.op (Y i)) =
      g ≫ c.π.app (Opposite.op (Y i))) :
    f = g := by
  refine hc.hom_ext (fun Z => F.2.hom_ext (hY.cover Z.unop) _ _ ?_)
  rintro ⟨W, a, ⟨i, ⟨b⟩⟩⟩
  simpa using h i =≫ F.1.map b.op

lemma sections_ext (F : Sheaf J (Type _)) {x y : F.1.sections}
    (h : ∀ (i : I), x.1 (Opposite.op (Y i)) = y.1 (Opposite.op (Y i))) :
    x = y := by
  ext W
  apply (Presieve.isSeparated_of_isSheaf J F.1
    ((isSheaf_iff_isSheaf_of_type _ _).1 F.2) _ (hY W.unop)).ext
  rintro T a ⟨i, ⟨b⟩⟩
  simpa using congr_arg (F.1.map b.op) (h i)

end CoversTop

end GrothendieckTopology

namespace Presheaf

variable (F : Cᵒᵖ ⥤ Type w) {I : Type*} (Y : I → C)

/-- A family of elements of a presheaf of types `F` indexed by a family of objects
`Y : I → C` consists of the data of an element in `F.obj (Opposite.op (Y i))` for all `i`. -/
def FamilyOfElementsOnObjects := ∀ (i : I), F.obj (Opposite.op (Y i))

namespace FamilyOfElementsOnObjects

variable {F Y}
variable (x : FamilyOfElementsOnObjects F Y)

/-- `x : FamilyOfElementsOnObjects F Y` is compatible if for any object `Z` such that
there exists a morphism `f : Z → Y i`, then the pullback of `x i` by `f` is independent
of `f` and `i`. -/
def IsCompatible (x : FamilyOfElementsOnObjects F Y) : Prop :=
  ∀ (Z : C) (i j : I) (f : Z ⟶ Y i) (g : Z ⟶ Y j),
    F.map f.op (x i) = F.map g.op (x j)

/-- A family of elements indexed by `Sieve.ofObjects Y X` that is induced by
`x : FamilyOfElementsOnObjects F Y`. See the equational lemma
`IsCompatible.familyOfElements_apply` which holds under the assumption `x.IsCompatible`. -/
noncomputable def familyOfElements (X : C) :
    Presieve.FamilyOfElements F (Sieve.ofObjects Y X).arrows :=
  fun _ _ hf => F.map hf.choose_spec.some.op (x _)

namespace IsCompatible

variable {x}

lemma familyOfElements_apply (hx : x.IsCompatible) {X Z : C} (f : Z ⟶ X) (i : I) (φ : Z ⟶ Y i) :
    familyOfElements x X f ⟨i, ⟨φ⟩⟩ = F.map φ.op (x i) := by
  apply hx

lemma familyOfElements_isCompatible (hx : x.IsCompatible) (X : C) :
    (familyOfElements x X).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i₁, ⟨φ₁⟩⟩ ⟨i₂, ⟨φ₂⟩⟩ _
  simpa [hx.familyOfElements_apply f₁ i₁ φ₁,
    hx.familyOfElements_apply f₂ i₂ φ₂] using hx Z i₁ i₂ (g₁ ≫ φ₁) (g₂ ≫ φ₂)

variable {J}

lemma existsUnique_section (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF : IsSheaf J F) :
    ∃! (s : F.sections), ∀ (i : I), s.1 (Opposite.op (Y i)) = x i := by
  have H := (isSheaf_iff_isSheaf_of_type _ _).1 hF
  apply existsUnique_of_exists_of_unique
  · let s := fun (X : C) => (H _ (hY X)).amalgamate _
      (hx.familyOfElements_isCompatible X)
    have hs : ∀ {X : C} (i : I) (f : X ⟶ Y i), s X = F.map f.op (x i) := fun {X} i f => by
      have h := Presieve.IsSheafFor.valid_glue (H _ (hY X))
          (hx.familyOfElements_isCompatible _) (𝟙 _) ⟨i, ⟨f⟩⟩
      simp only [op_id, F.map_id, types_id_apply] at h
      exact h.trans (hx.familyOfElements_apply _ _ _)
    have hs' : ∀ {W X : C} (a : W ⟶ X) (i : I) (_ : W ⟶ Y i), F.map a.op (s X) = s W := by
      intro W X a i b
      rw [hs i b]
      exact (Presieve.IsSheafFor.valid_glue (H _ (hY X))
        (hx.familyOfElements_isCompatible _) a ⟨i, ⟨b⟩⟩).trans (familyOfElements_apply hx _ _ _)
    refine ⟨⟨fun X => s X.unop, ?_⟩, fun i => (hs i (𝟙 (Y i))).trans (by simp)⟩
    rintro ⟨Y₁⟩ ⟨Y₂⟩ ⟨f : Y₂ ⟶ Y₁⟩
    change F.map f.op (s Y₁) = s Y₂
    apply (Presieve.isSeparated_of_isSheaf J F H _ (hY Y₂)).ext
    rintro Z φ ⟨i, ⟨g⟩⟩
    rw [hs' φ i g, ← hs' (φ ≫ f) i g, op_comp, F.map_comp]
    rfl
  · intro y₁ y₂ hy₁ hy₂
    exact hY.sections_ext ⟨F, hF⟩ (fun i => by rw [hy₁, hy₂])

variable (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF : IsSheaf J F)

/-- The section of a sheaf of types which lifts a compatible family of elements indexed
by objects which cover the terminal object. -/
noncomputable def section_ : F.sections := (hx.existsUnique_section hY hF).choose

@[simp]
lemma section_apply (i : I) : (hx.section_ hY hF).1 (Opposite.op (Y i)) = x i :=
  (hx.existsUnique_section hY hF).choose_spec.1 i

end IsCompatible

end FamilyOfElementsOnObjects

end Presheaf

end CategoryTheory
