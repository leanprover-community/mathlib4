/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Generator.Basic

/-!
# Strong generators

A set of objects `S` in a category `C` is a strong generator if it is a
generator (in the sense that `IsSeparating S` holds) such that for any
proper subobject `A ⊂ X`, there exists a morphism `G ⟶ X` from an
object in `S` which does not factor through `A`.

The main result is the lemma `isStrongGenerator_iff_exists_extremalEpi` which
says that if `S` is `w`-small, `C` is locally `w`-small and
has coproducts of size `w`, then `S` is a strong generator iff any
object of `C` is the target of an extremal epimorphism from a coproduct of
objects in `S`. A similar iff lemma for `IsSeparating` is also obtained.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (S : Set C)

/-- A set of objects is a strong generator if it is separating and for any
proper subobject `A ⊂ X`, there exists a morphism `G ⟶ X` from an
object in `S` which does not factor through `A`. -/
def IsStrongGenerator : Prop :=
  IsSeparating S ∧ ∀ ⦃X : C⦄ (A : Subobject X),
    (∀ (G : S) (f : G.1 ⟶ X), Subobject.Factors A f) → A = ⊤

variable {S}

lemma isStrongGenerator_iff :
    IsStrongGenerator S ↔ IsSeparating S ∧
      ∀ ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i],
        (∀ (G : S), Function.Surjective (fun (f : G.1 ⟶ X) ↦ f ≫ i)) → IsIso i := by
  refine ⟨fun ⟨hS₁, hS₂⟩ ↦ ⟨hS₁, fun X Y i _ h ↦ ?_⟩,
    fun ⟨hS₁, hS₂⟩ ↦ ⟨hS₁, fun X A hA ↦ ?_⟩⟩
  · rw [Subobject.isIso_iff_mk_eq_top]
    refine hS₂ _ (fun G g ↦ ?_)
    rw [Subobject.mk_factors_iff]
    exact h G g
  · rw [← Subobject.isIso_arrow_iff_eq_top]
    exact hS₂ A.arrow (fun G g ↦ ⟨_, Subobject.factorThru_arrow _ _ (hA G g)⟩)

namespace IsStrongGenerator

section

variable (hS : IsStrongGenerator S)

include hS

lemma isSeparating : IsSeparating S := hS.1

lemma subobject_eq_top {X : C} {A : Subobject X}
    (hA : ∀ (G : S) (f : G.1 ⟶ X), Subobject.Factors A f) :
    A = ⊤ :=
  hS.2 _ hA

lemma isIso_of_mono ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i]
    (hi : ∀ (G : S), Function.Surjective (fun (f : G.1 ⟶ X) ↦ f ≫ i)) : IsIso i :=
  (isStrongGenerator_iff.1 hS).2 i hi

lemma exists_of_subobject_ne_top {X : C} {A : Subobject X} (hA : A ≠ ⊤) :
    ∃ (G : S) (f : G.1 ⟶ X), ¬ Subobject.Factors A f := by
  by_contra!
  exact hA (hS.subobject_eq_top this)

lemma exists_of_mono_not_isIso {X Y : C} (i : X ⟶ Y) [Mono i] (hi : ¬ IsIso i) :
    ∃ (G : S) (g : G.1 ⟶ Y), ∀ (f : G.1 ⟶ X), f ≫ i ≠ g := by
  by_contra!
  exact hi (hS.isIso_of_mono i this)

end

end IsStrongGenerator

section

variable (S) [HasCoproducts.{w} C] [LocallySmall.{w} C] [Small.{w} S] (X : C)

/-- Given `S : Set C` and `X : C`, this is the family of source objects
in the family of all maps `G ⟶ X` with `G ∈ S`. -/
abbrev coproductOfSet.obj (p : Σ (s : S), s.1 ⟶ X) : C := p.1.1

lemma coproductOfSet.hasCoproduct :
    HasCoproduct (coproductOfSet.obj S X) :=
  hasColimit_of_equivalence_comp
    (Discrete.equivalence (equivShrink.{w} _)).symm

/-- Given `S : Set C` and `X : C`, this is the coproduct of
`G` indexed by the type of all maps `G ⟶ X` with `G ∈ S`. -/
noncomputable def coproductOfSet (X : C) : C :=
  have := coproductOfSet.hasCoproduct S X
  ∐ (coproductOfSet.obj S X)

namespace coproductOfSet

/-- The canonical morphism `coproductOfSet S X ⟶ X`. -/
noncomputable def π (X : C) : coproductOfSet S X ⟶ X :=
  have := coproductOfSet.hasCoproduct S X
  Sigma.desc (fun p ↦ p.2)

section

variable {S} {X : C} (s : S) (f : s.1 ⟶ X)

/-- The inclusion morphisms in the coproduct `coproductOfSet S X`. -/
noncomputable def ι : s.1 ⟶ coproductOfSet S X :=
  have := coproductOfSet.hasCoproduct S X
  Sigma.ι (coproductOfSet.obj S X) ⟨s, f⟩

@[reassoc (attr := simp)]
lemma ι_π : ι s f ≫ π S X = f := by simp [ι, π]

end

end coproductOfSet

end

namespace IsSeparating

lemma epi_coproductOfSetπ (hS : IsSeparating S)
    [HasCoproducts.{w} C] [LocallySmall.{w} C] [Small.{w} S] (X : C) :
    Epi (coproductOfSet.π S X) where
  left_cancellation {Z} f g h :=
    hS _ _ (fun G hG p ↦ by simpa using coproductOfSet.ι ⟨_, hG⟩ p ≫= h)

lemma mk_of_exists_epi
    (hS : ∀ (X : C), ∃ (ι : Type w) (s : ι → S) (c : Cofan (fun i ↦ (s i).1)) (_ : IsColimit c)
      (p : c.pt ⟶ X), Epi p) :
    IsSeparating S := by
  intro X Y f g h
  obtain ⟨ι, s, c, hc, p, _⟩ := hS X
  rw [← cancel_epi p]
  exact Cofan.IsColimit.hom_ext hc _ _
    (fun i ↦ by simpa using h _ (s i).2 (c.inj i ≫ p))

end IsSeparating

lemma isSeparating_iff_exists_epi
    [HasCoproducts.{w} C] [LocallySmall.{w} C] [Small.{w} S] :
    IsSeparating S ↔
      ∀ (X : C), ∃ (ι : Type w) (s : ι → S) (c : Cofan (fun i ↦ (s i).1)) (_ : IsColimit c)
        (p : c.pt ⟶ X), Epi p := by
  refine ⟨fun hS X ↦ ?_, fun hS ↦ .mk_of_exists_epi hS⟩
  have := coproductOfSet.hasCoproduct S X
  exact ⟨_, fun j ↦ ((equivShrink (Σ (s : S), s.1 ⟶ X)).symm j).1, _,
    (colimit.isColimit (Discrete.functor (coproductOfSet.obj S X))).whiskerEquivalence
      ((Discrete.equivalence (equivShrink.{w} _))).symm, _,
      hS.epi_coproductOfSetπ X⟩

namespace IsStrongGenerator

lemma extremalEpi_coproductOfSetπ
    (hS : IsStrongGenerator S) [HasCoproducts.{w} C] [LocallySmall.{w} C]
    [Small.{w} S] (X : C) :
    ExtremalEpi (coproductOfSet.π S X) where
  toEpi := hS.isSeparating.epi_coproductOfSetπ X
  isIso {Z} p i fac _ := hS.isIso_of_mono _
    (fun G f ↦ ⟨coproductOfSet.ι G f ≫ p, by simp [fac]⟩)

lemma mk_of_exists_extremalEpi
    (hS : ∀ (X : C), ∃ (ι : Type w) (s : ι → S) (c : Cofan (fun i ↦ (s i).1)) (_ : IsColimit c)
      (p : c.pt ⟶ X), ExtremalEpi p) :
    IsStrongGenerator S := by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_epi.{w} (fun X ↦ ?_), fun X Y i _ hi ↦ ?_⟩
  · obtain ⟨ι, s, c, hc, p, _⟩ := hS X
    exact ⟨ι, s, c, hc, p, inferInstance⟩
  · obtain ⟨ι, s, c, hc, p, _⟩ := hS Y
    replace hi (j : ι) := hi (s j) (c.inj j ≫ p)
    choose φ hφ using hi
    exact ExtremalEpi.isIso p (Cofan.IsColimit.desc hc φ) _
      (Cofan.IsColimit.hom_ext hc _ _ (by simp [hφ]))

end IsStrongGenerator

lemma isStrongGenerator_iff_exists_extremalEpi
    [HasCoproducts.{w} C] [LocallySmall.{w} C] [Small.{w} S] :
    IsStrongGenerator S ↔
      ∀ (X : C), ∃ (ι : Type w) (s : ι → S) (c : Cofan (fun i ↦ (s i).1)) (_ : IsColimit c)
        (p : c.pt ⟶ X), ExtremalEpi p := by
  refine ⟨fun hS X ↦ ?_, fun hS ↦ .mk_of_exists_extremalEpi hS⟩
  have := coproductOfSet.hasCoproduct S X
  exact ⟨_, fun j ↦ ((equivShrink (Σ (s : S), s.1 ⟶ X)).symm j).1, _,
    (colimit.isColimit (Discrete.functor (coproductOfSet.obj S X))).whiskerEquivalence
      ((Discrete.equivalence (equivShrink.{w} _))).symm, _,
      hS.extremalEpi_coproductOfSetπ X⟩

end CategoryTheory
