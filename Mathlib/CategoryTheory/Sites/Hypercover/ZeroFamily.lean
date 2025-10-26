/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Defining precoverages via pre-`0`-hypercovers

A precoverage is a condition on all presieves. In some applications, it is practical
to instead define a condition on all pre-`0`-hypercovers. Such a condition
for every object is a pre-`0`-hypercover family if these conditions are
invariant under deduplication.
-/

universe w' w v u

namespace CategoryTheory
open Limits

variable {C : Type u} [Category.{v} C]

variable (C) in
/--
A pre-`0`-hypercover family on `C` is a property on the category of pre-`0`-hypercovers
for every `X : C` that is invariant under deduplication.
The data of a pre-`0`-hypercover family is the same as the data of a precoverage
(see: `Precoverage.equivPreZeroHypercoverFamily`).
-/
@[ext]
structure PreZeroHypercoverFamily where
  /-- The condition on pre-`0`-hypercovers for every object. -/
  property ⦃X : C⦄ : ObjectProperty (PreZeroHypercover.{max u v} X)
  iff_shrink {X : C} {E : PreZeroHypercover.{max u v} X} : property E ↔ property E.shrink

instance : CoeFun (PreZeroHypercoverFamily C)
    fun _ ↦ ⦃X : C⦄ → (E : PreZeroHypercover.{max u v} X) → Prop where
  coe P := P.property

/-- The induced condition on presieves in `C`, given by a pre-`0`-hypercover family. -/
inductive PreZeroHypercoverFamily.presieve (P : PreZeroHypercoverFamily C) {X : C} :
    Presieve X → Prop where
  | mk (E : PreZeroHypercover.{max u v} X) : P E → presieve P E.presieve₀

/-- The associated precoverage to a pre-`0`-hypercover family. -/
def PreZeroHypercoverFamily.precoverage (P : PreZeroHypercoverFamily C) :
    Precoverage C where
  coverings _ R := P.presieve R

lemma PreZeroHypercoverFamily.mem_precoverage_iff {P : PreZeroHypercoverFamily C} {X : C}
    {R : Presieve X} :
    R ∈ P.precoverage X ↔ ∃ (E : PreZeroHypercover.{max u v} X), P E ∧ R = E.presieve₀ :=
  ⟨fun ⟨E, hE⟩ ↦ ⟨E, hE, rfl⟩, fun ⟨_, hE, h⟩ ↦ h ▸ ⟨_, hE⟩⟩

@[simp]
lemma PreZeroHypercover.presieve₀_mem_precoverage_iff {P : PreZeroHypercoverFamily C} {X : C}
    {E : PreZeroHypercover.{max u v} X} :
    E.presieve₀ ∈ P.precoverage X ↔ P E := by
  refine ⟨fun h ↦ ?_, fun h ↦ .mk _ h⟩
  rw [PreZeroHypercoverFamily.mem_precoverage_iff] at h
  obtain ⟨F, h, heq⟩ := h
  rw [P.iff_shrink] at h ⊢
  rwa [PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀ heq]

/-- The associated pre-`0`-hypercover family to a precoverage. -/
@[simps]
def Precoverage.preZeroHypercoverFamily (K : Precoverage C) :
    PreZeroHypercoverFamily C where
  property X E := E.presieve₀ ∈ K X
  iff_shrink {X} E := by simp

variable (C) in
/-- Giving a precoverage on a category is the same as giving a predicate
on every pre-`0`-hypercover that is stable under deduplication. -/
def Precoverage.equivPreZeroHypercoverFamily :
    Precoverage C ≃ PreZeroHypercoverFamily C where
  toFun K := K.preZeroHypercoverFamily
  invFun P := P.precoverage
  left_inv K := by
    ext X R
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    simp
  right_inv P := by cat_disch

lemma Precoverage.HasIsos.of_preZeroHypercoverFamily {P : PreZeroHypercoverFamily C}
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsIso f], P (.singleton f)) :
    P.precoverage.HasIsos where
  mem_coverings_of_isIso {S T} f hf := by
    rw [← PreZeroHypercover.presieve₀_singleton.{_, _, max u v}]
    refine .mk _ (h _)

lemma Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms
    {P : PreZeroHypercoverFamily C}
    (h₁ : ∀ {X : C}, (P (X := X)).IsClosedUnderIsomorphisms)
    (h₂ : ∀ {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{max u v} Y)
      [∀ (i : E.I₀), HasPullback f (E.f i)], P E → P (E.pullback₁ f)) :
    Precoverage.IsStableUnderBaseChange P.precoverage where
  mem_coverings_of_isPullback {ι} S X f hf Y g Z p₁ p₂ h := by
    let E : PreZeroHypercover S := ⟨ι, X, f⟩
    have (i : E.I₀) : HasPullback g (E.f i) := (h i).hasPullback
    let F : PreZeroHypercover Y := ⟨_, _, p₁⟩
    let e : F ≅ E.pullback₁ g :=
      PreZeroHypercover.isoMk (Equiv.refl _) (fun i ↦ (h i).isoPullback)
    change F.presieve₀ ∈ _
    rw [F.presieve₀_mem_precoverage_iff, (P (X := Y)).prop_iff_of_iso e]
    refine h₂ _ _ ?_
    rwa [← E.presieve₀_mem_precoverage_iff]

lemma Precoverage.IsStableUnderComposition.of_preZeroHypercoverFamily
    {P : PreZeroHypercoverFamily C}
    (h : ∀ {X : C} (E : PreZeroHypercover.{max u v} X)
      (F : ∀ i, PreZeroHypercover.{max u v} (E.X i)),
      P E → (∀ i, P (F i)) → P (E.bind F)) :
    Precoverage.IsStableUnderComposition P.precoverage where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    let E : PreZeroHypercover S := ⟨_, _, f⟩
    let F (i : ι) : PreZeroHypercover (E.X i) := ⟨_, _, g i⟩
    refine (E.bind F).presieve₀_mem_precoverage_iff.mpr (h _ _ ?_ fun i ↦ ?_)
    · rwa [← E.presieve₀_mem_precoverage_iff]
    · rw [← (F i).presieve₀_mem_precoverage_iff]
      exact hg i

end CategoryTheory
