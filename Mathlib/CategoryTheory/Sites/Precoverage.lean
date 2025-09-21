/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Preserves.Creates.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!

# Precoverages

A precoverage `K` on a category `C` is a set of presieves associated to every object `X : C`,
called "covering presieves".
There are no conditions on this set. Common extensions of a precoverage are:

- `CategoryTheory.Coverage`: A coverage is a precoverage that satisfies a pullback compatibility
  condition, saying that whenever `S` is a covering presieve on `X` and `f : Y ⟶ X` is a morphism,
  then there exists some covering sieve `T` on `Y` such that `T` factors through `S` along `f`.
- `CategoryTheory.Pretopology`: If `C` has pullbacks, a pretopology on `C` is a precoverage that
  has isomorphisms and is stable under pullback and refinement.

These two are defined in later files. For precoverages, we define stability conditions:

- `CategoryTheory.Precoverage.HasIsos`: Singleton presieves by isomorphisms are covering.
- `CategoryTheory.Precoverage.IsStableUnderBaseChange`: The pullback of a covering presieve is again
  covering.
- `CategoryTheory.Precoverage.IsStableUnderComposition`: Refining a covering presieve by covering
  presieves yields a covering presieve.

-/

universe w w' v u

namespace CategoryTheory

/-- A precoverage is a collection of *covering* presieves on every object `X : C`.
See `CategoryTheory.Coverage` and `CategoryTheory.Pretopology` for common extensions of this. -/
@[ext]
structure Precoverage (C : Type*) [Category C] where
  /-- The collection of covering presieves for an object `X`. -/
  coverings : ∀ (X : C), Set (Presieve X)

namespace Precoverage

variable {C : Type u} [Category.{v} C]

instance : CoeFun (Precoverage C) (fun _ => (X : C) → Set (Presieve X)) where
  coe := coverings

instance : PartialOrder (Precoverage C) where
  le A B := A.coverings ≤ B.coverings
  le_refl _ _ := le_refl _
  le_trans _ _ _ h1 h2 X := le_trans (h1 X) (h2 X)
  le_antisymm _ _ h1 h2 := Precoverage.ext <| funext <|
    fun X => le_antisymm (h1 X) (h2 X)

instance : Min (Precoverage C) where
  min A B := ⟨A.coverings ⊓ B.coverings⟩

instance : Max (Precoverage C) where
  max A B := ⟨A.coverings ⊔ B.coverings⟩

instance : SupSet (Precoverage C) where
  sSup A := ⟨⨆ K ∈ A, K.coverings⟩

instance : InfSet (Precoverage C) where
  sInf A := ⟨⨅ K ∈ A, K.coverings⟩

instance : Top (Precoverage C) where
  top.coverings _ := .univ

instance : Bot (Precoverage C) where
  bot.coverings _ := ∅

instance : CompleteLattice (Precoverage C) :=
  Function.Injective.completeLattice Precoverage.coverings (fun _ _ hab ↦ Precoverage.ext hab)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl

/-- A precoverage has isomorphisms if singleton presieves by isomorphisms are covering. -/
class HasIsos (J : Precoverage C) : Prop where
  mem_coverings_of_isIso {S T : C} (f : S ⟶ T) [IsIso f] : .singleton f ∈ J T

/-- A precoverage is stable under base change if pullbacks of covering presieves
are covering presieves.
Note: This is stronger than the analogous requirement for a `Pretopology`, because
`IsPullback` does not imply equality with the (arbitrarily) chosen pullbacks in `C`. -/
class IsStableUnderBaseChange (J : Precoverage C) : Prop where
  mem_coverings_of_isPullback {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (hR : Presieve.ofArrows X f ∈ J S) {Y : C} (g : Y ⟶ S)
    {P : ι → C} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    .ofArrows P p₁ ∈ J Y

/-- A precoverage is stable under composition if the indexed composition
of coverings is again a covering.
Note: This is stronger than the analogous requirement for a `Pretopology`, because
this is in general not equal to a `Presieve.bind`. -/
class IsStableUnderComposition (J : Precoverage C) : Prop where
  comp_mem_coverings {ι : Type w}
    {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ J S)
    {σ : ι → Type w'} {Y : ∀ (i : ι), σ i → C}
    (g : ∀ i j, Y i j ⟶ X i) (hg : ∀ i, Presieve.ofArrows (Y i) (g i) ∈ J (X i)) :
    .ofArrows (fun p : Σ i, σ i ↦ Y _ p.2) (fun _ ↦ g _ _ ≫ f _) ∈ J S

/-- A precoverage is stable under `⊔` if whenever `R` and `S` are coverings,
also `R ⊔ S` is a covering. -/
class IsStableUnderSup (J : Precoverage C) where
  sup_mem_coverings {X : C} {R S : Presieve X} (hR : R ∈ J X) (hS : S ∈ J X) :
    R ⊔ S ∈ J X

/-- A precoverage has pullbacks, if every covering presieve has pullbacks along arbitrary
morphisms. -/
class HasPullbacks (J : Precoverage C) where
  hasPullbacks_of_mem {X Y : C} {R : Presieve Y} (f : X ⟶ Y) (hR : R ∈ J Y) : R.HasPullbacks f

alias mem_coverings_of_isIso := HasIsos.mem_coverings_of_isIso
alias mem_coverings_of_isPullback := IsStableUnderBaseChange.mem_coverings_of_isPullback
alias comp_mem_coverings := IsStableUnderComposition.comp_mem_coverings
alias sup_mem_coverings := IsStableUnderSup.sup_mem_coverings
alias hasPullbacks_of_mem := HasPullbacks.hasPullbacks_of_mem

lemma pullbackArrows_mem {J : Precoverage C} [IsStableUnderBaseChange.{max u v} J]
    {X Y : C} (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ J Y) [R.HasPullbacks f] :
    R.pullbackArrows f ∈ J X := by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : Limits.HasPullback (g i) f := Presieve.hasPullback f (Presieve.ofArrows.mk i)
  rw [← Presieve.ofArrows_pullback]
  exact mem_coverings_of_isPullback _ hR _ _ _ fun i ↦ (IsPullback.of_hasPullback _ _).flip

instance (J K : Precoverage C) [HasIsos J] [HasIsos K] : HasIsos (J ⊓ K) where
  mem_coverings_of_isIso f _ := ⟨mem_coverings_of_isIso f, mem_coverings_of_isIso f⟩

instance (J K : Precoverage C) [IsStableUnderBaseChange.{w} J] [IsStableUnderBaseChange.{w} K] :
    IsStableUnderBaseChange.{w} (J ⊓ K) where
  mem_coverings_of_isPullback _ hf _ _ _ _ _ h :=
    ⟨mem_coverings_of_isPullback _ hf.1 _ _ _ h, mem_coverings_of_isPullback _ hf.2 _ _ _ h⟩

instance (J K : Precoverage C) [IsStableUnderComposition.{w, w'} J]
    [IsStableUnderComposition.{w, w'} K] : IsStableUnderComposition.{w, w'} (J ⊓ K) where
  comp_mem_coverings _ h _ _ _ H :=
    ⟨comp_mem_coverings _ h.1 _ fun i ↦ (H i).1, comp_mem_coverings _ h.2 _ fun i ↦ (H i).2⟩

instance (J K : Precoverage C) [IsStableUnderSup J] [IsStableUnderSup K] :
    IsStableUnderSup (J ⊓ K) where
  sup_mem_coverings hR hS := ⟨J.sup_mem_coverings hR.1 hS.1, K.sup_mem_coverings hR.2 hS.2⟩

section Functoriality

variable {D : Type*} [Category D] {F : C ⥤ D}

variable {J K : Precoverage D}

open Limits

/-- If `J` is a precoverage on `D`, we obtain a precoverage on `C` by declaring a presieve on `D`
to be covering if its image under `F` is. -/
def comap (F : C ⥤ D) (J : Precoverage D) : Precoverage C where
  coverings Y R := R.map F ∈ J (F.obj Y)

@[simp]
lemma mem_comap_iff {X : C} {R : Presieve X} :
    R ∈ J.comap F X ↔ R.map F ∈ J (F.obj X) := Iff.rfl

lemma comap_inf : (J ⊓ K).comap F = J.comap F ⊓ K.comap F := rfl

instance [HasIsos J] : HasIsos (J.comap F) where
  mem_coverings_of_isIso {S T} f hf := by simpa using mem_coverings_of_isIso (F.map f)

instance [IsStableUnderComposition.{w', w} J] :
    IsStableUnderComposition.{w', w} (J.comap F) where
  comp_mem_coverings {ι} S Y f hf σ Z g hg := by
    simp at hf hg ⊢
    exact J.comp_mem_coverings _ hf _ hg

instance [PreservesLimitsOfShape WalkingCospan F] [IsStableUnderBaseChange.{w} J] :
    IsStableUnderBaseChange.{w} (J.comap F) where
  mem_coverings_of_isPullback {ι} S Y f hf Z g P p₁ p₂ h := by
    simp only [mem_comap_iff, Presieve.map_ofArrows] at hf ⊢
    exact mem_coverings_of_isPullback _ hf _ _ _
      fun i ↦ CategoryTheory.Functor.map_isPullback F (h i)

instance [CreatesLimitsOfShape WalkingCospan F] [HasPullbacks J] : HasPullbacks (J.comap F) where
  hasPullbacks_of_mem {X Y} R f hR := by
    refine ⟨fun {Z g} hg ↦ ?_⟩
    have : (Presieve.map F R).HasPullbacks (F.map f) := J.hasPullbacks_of_mem (F.map f) hR
    have : HasPullback (F.map g) (F.map f) := (R.map F).hasPullback _ (R.map_map hg)
    exact .of_createsLimit F g f

end Functoriality

end Precoverage

end CategoryTheory
