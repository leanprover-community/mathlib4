/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Generator.Basic

/-!
# Strong generators

If `P : ObjectProperty C`, we say that `P` is a strong generator if it is a
generator (in the sense that `IsSeparating P` holds) such that for any
proper subobject `A ⊂ X`, there exists a morphism `G ⟶ X` which does not factor
through `A` from an object satisfying `P`.

The main result is the lemma `isStrongGenerator_iff_exists_extremalEpi` which
says that if `P` is `w`-small, `C` is locally `w`-small and
has coproducts of size `w`, then `P` is a strong generator iff any
object of `C` is the target of an extremal epimorphism from a coproduct of
objects satisfying `P`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

namespace CategoryTheory

open Limits


namespace ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- A property `P : ObjectProperty C` is a strong generator
if it is separating and for any proper subobject `A ⊂ X`, there exists
a morphism `G ⟶ X` which does not factor through `A` from an object
such that `P G` holds. -/
def IsStrongGenerator : Prop :=
  P.IsSeparating ∧ ∀ ⦃X : C⦄ (A : Subobject X),
    (∀ (G : C) (_ : P G) (f : G ⟶ X), Subobject.Factors A f) → A = ⊤

variable {P}

lemma isStrongGenerator_iff :
    P.IsStrongGenerator ↔ P.IsSeparating ∧
      ∀ ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i],
        (∀ (G : C) (_ : P G), Function.Surjective (fun (f : G ⟶ X) ↦ f ≫ i)) → IsIso i := by
  refine ⟨fun ⟨hS₁, hS₂⟩ ↦ ⟨hS₁, fun X Y i _ h ↦ ?_⟩,
    fun ⟨hS₁, hS₂⟩ ↦ ⟨hS₁, fun X A hA ↦ ?_⟩⟩
  · rw [Subobject.isIso_iff_mk_eq_top]
    refine hS₂ _ (fun G hG g ↦ ?_)
    rw [Subobject.mk_factors_iff]
    exact h G hG g
  · rw [← Subobject.isIso_arrow_iff_eq_top]
    exact hS₂ A.arrow (fun G hG g ↦ ⟨_, Subobject.factorThru_arrow _ _ (hA G hG g)⟩)

namespace IsStrongGenerator

section

variable (hP : P.IsStrongGenerator)

include hP

lemma isSeparating : P.IsSeparating := hP.1

lemma subobject_eq_top {X : C} {A : Subobject X}
    (hA : ∀ (G : C) (_ : P G) (f : G ⟶ X), Subobject.Factors A f) :
    A = ⊤ :=
  hP.2 _ hA

lemma isIso_of_mono ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i]
    (hi : ∀ (G : C) (_ : P G), Function.Surjective (fun (f : G ⟶ X) ↦ f ≫ i)) : IsIso i :=
  (isStrongGenerator_iff.1 hP).2 i hi

lemma exists_of_subobject_ne_top {X : C} {A : Subobject X} (hA : A ≠ ⊤) :
    ∃ (G : C) (_ : P G) (f : G ⟶ X), ¬ Subobject.Factors A f := by
  by_contra!
  exact hA (hP.subobject_eq_top this)

lemma exists_of_mono_not_isIso {X Y : C} (i : X ⟶ Y) [Mono i] (hi : ¬ IsIso i) :
    ∃ (G : C) (_ : P G) (g : G ⟶ Y), ∀ (f : G ⟶ X), f ≫ i ≠ g := by
  by_contra!
  exact hi (hP.isIso_of_mono i this)

end

end IsStrongGenerator

namespace IsStrongGenerator

lemma mk_of_exists_extremalEpi
    (hS : ∀ (X : C), ∃ (ι : Type w) (s : ι → C) (_ : ∀ i, P (s i)) (c : Cofan s) (_ : IsColimit c)
      (p : c.pt ⟶ X), ExtremalEpi p) :
    P.IsStrongGenerator := by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_epi.{w} (fun X ↦ ?_), fun X Y i _ hi ↦ ?_⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS X
    exact ⟨ι, s, hs, c, hc, p, inferInstance⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS Y
    replace hi (j : ι) := hi (s j) (hs j) (c.inj j ≫ p)
    choose φ hφ using hi
    exact ExtremalEpi.isIso p (Cofan.IsColimit.desc hc φ) _
      (Cofan.IsColimit.hom_ext hc _ _ (by simp [hφ]))

lemma extremalEpi_coproductFrom
    (hP : IsStrongGenerator P) (X : C) [HasCoproduct (P.coproductFromFamily X)] :
    ExtremalEpi (P.coproductFrom X) where
  toEpi := hP.isSeparating.epi_coproductFrom X
  isIso p i fac _ := hP.isIso_of_mono _ (fun G hG f ↦ ⟨P.ιCoproductFrom f hG ≫ p, by simp [fac]⟩)

end IsStrongGenerator

lemma isStrongGenerator_iff_exists_extremalEpi
    [HasCoproducts.{w} C] [LocallySmall.{w} C] [ObjectProperty.Small.{w} P] :
    P.IsStrongGenerator ↔
      ∀ (X : C), ∃ (ι : Type w) (s : ι → C) (_ : ∀ i, P (s i)) (c : Cofan s) (_ : IsColimit c)
        (p : c.pt ⟶ X), ExtremalEpi p := by
  refine ⟨fun hP X ↦ ?_, fun hP ↦ .mk_of_exists_extremalEpi hP⟩
  have := hasCoproductsOfShape_of_small.{w} C (CostructuredArrow P.ι X)
  have := (coproductIsCoproduct (P.coproductFromFamily X)).whiskerEquivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm
  refine ⟨_, fun j ↦ ((equivShrink.{w} (CostructuredArrow P.ι X)).symm j).left.1,
    fun j ↦ ((equivShrink.{w} _).symm j).1.2, _,
    (coproductIsCoproduct (P.coproductFromFamily X)).whiskerEquivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm, _, hP.extremalEpi_coproductFrom X⟩

end ObjectProperty

end CategoryTheory
