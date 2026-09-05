/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Finite resolutions by objects satisfying `P : ObjectProperty C`

## Main definitions

Let `C` be a category, `P : ObjectProperty C` be a property of objects in `C`.

* `CategoryTheory.ObjectProperty.hasFiniteResolutionOfLength`:
  We say that `X : C` has a `P`-resolution of length `n` if there exists an
  exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ X ⟶ 0` such that each `Eᵢ : C` satisfies `P`.
* `CategoryTheory.ObjectProperty.hasFiniteResolution`:
  We say that `X : C` has a finite `P`-resolution if it has a `P`-resolution of some finite length.

## Implementation notes

Rather than defining `hasFiniteResolutionOfLength` in terms of explicit exact sequences,
we define it inductively: `X` has a `P`-resolution of length `0` if `X` satisfies `P`, and
it has a `P`-resolution of length `n + 1` if there exists a short exact sequence
`0 ⟶ K ⟶ E ⟶ X ⟶ 0` such that `E` satisfies `P` and `K` has a `P`-resolution of length `n`.

## TODO

* Construct a chain complex `K` whose terms satisfy `P` with a quasi-isomorphism from `K` to the
  single complex on `X` when `C` is abelian and `X` has a finite `P`-resolution.
-/

public section

universe v' v u' u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Let `C` be a category, `P : ObjectProperty C` be a property of objectsin `C`.
We say that `X : C` has a `P`-resolution of length `n` if there exists an
exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ X ⟶ 0` such that each `Eᵢ : C` satisfies `P`.

Rather than defining `hasFiniteResolutionOfLength` in terms of explicit exact sequences,
we define it inductively: `X` has a `P`-resolution of length `0` if `X` satisfies `P`, and
it has a `P`-resolution of length `n + 1` if there exists a short exact sequence
`0 ⟶ K ⟶ E ⟶ X ⟶ 0` such that `E` satisfies `P` and `K` has a `P`-resolution of length `n`. -/
inductive hasFiniteResolutionOfLength (P : ObjectProperty C) : ℕ → ObjectProperty C
  | zero (X : C) (hX : P X) : hasFiniteResolutionOfLength P 0 X
  | succ (S : ShortComplex C) (n : ℕ) (hS : S.ShortExact) (h₂ : P S.X₂)
      (h₁ : hasFiniteResolutionOfLength P n S.X₁) : hasFiniteResolutionOfLength P (n + 1) S.X₃

/-- Let `C` be a category, `P : ObjectProperty C` be a property of objects in `C`.
We say that `X : C` has a finite `P`-resolution if it has a `P`-resolution of some finite length. -/
def hasFiniteResolution (P : ObjectProperty C) : ObjectProperty C :=
  ⨆ n : ℕ, P.hasFiniteResolutionOfLength n

variable {P Q : ObjectProperty C} {X : C} {n : ℕ}

@[simp]
theorem hasFiniteResolution_iff :
    P.hasFiniteResolution X ↔ ∃ n, P.hasFiniteResolutionOfLength n X :=
  prop_iSup_iff _ X

namespace hasFiniteResolutionOfLength

theorem property : P = P.hasFiniteResolutionOfLength 0 :=
  le_antisymm hasFiniteResolutionOfLength.zero fun _ hX ↦
    match hX with
    | zero _ hX => hX

theorem monotone (hPQ : P ≤ Q) :
    P.hasFiniteResolutionOfLength n ≤ Q.hasFiniteResolutionOfLength n := by
  intro X hX
  induction hX with
  | zero X hX => exact hasFiniteResolutionOfLength.zero X (hPQ X hX)
  | succ S n hS h₂ _ ih => exact hasFiniteResolutionOfLength.succ S n hS (hPQ S.X₂ h₂) ih

theorem property_of_isClosedUnderQuotients [P.IsClosedUnderQuotients] :
    P.hasFiniteResolutionOfLength n ≤ P := fun X hX ↦
  match hX with
  | zero _ hX => hX
  | succ S _ hS h₂ _ => P.prop_X₃_of_shortExact hS h₂

instance [P.IsClosedUnderIsomorphisms] :
    (P.hasFiniteResolutionOfLength n).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX :=
    match hX with
    | zero _ hX => hasFiniteResolutionOfLength.zero Y (P.prop_of_iso e hX)
    | succ S n hS h₂ h₁ =>
      let T : ShortComplex C := ShortComplex.mk S.f (S.g ≫ e.hom) (by simp)
      let eS : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp [T]) (by simp [T])
      hasFiniteResolutionOfLength.succ T n (ShortComplex.shortExact_of_iso eS hS) h₂ h₁

theorem map_exactFunctor {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
    {Q : ObjectProperty D} (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (hF : P ≤ Q.inverseImage F) :
    P.hasFiniteResolutionOfLength n ≤ (Q.hasFiniteResolutionOfLength n).inverseImage F := by
  intro X hX
  induction hX with
  | zero X hX => exact hasFiniteResolutionOfLength.zero (F.obj X) (hF X hX)
  | succ S n hS h₂ _ ih =>
      exact hasFiniteResolutionOfLength.succ (S.map F) n (hS.map_of_exact F) (hF S.X₂ h₂) ih

theorem le_hasFiniteResolution : P.hasFiniteResolutionOfLength n ≤ P.hasFiniteResolution :=
  le_iSup _ n

end hasFiniteResolutionOfLength

namespace hasFiniteResolution

theorem of_property (hX : P X) : P.hasFiniteResolution X :=
  hasFiniteResolutionOfLength.le_hasFiniteResolution X (.zero X hX)

instance [P.Is X] : P.hasFiniteResolution.Is X := ⟨of_property (P.prop_of_is X)⟩

theorem monotone (hPQ : P ≤ Q) : P.hasFiniteResolution ≤ Q.hasFiniteResolution :=
  iSup_mono fun _ ↦ hasFiniteResolutionOfLength.monotone hPQ

theorem property_of_isClosedUnderQuotients [P.IsClosedUnderQuotients] :
    P.hasFiniteResolution ≤ P :=
  iSup_le fun _ ↦ hasFiniteResolutionOfLength.property_of_isClosedUnderQuotients

instance [P.IsClosedUnderIsomorphisms] : P.hasFiniteResolution.IsClosedUnderIsomorphisms :=
  inferInstanceAs (⨆ n : ℕ, P.hasFiniteResolutionOfLength n).IsClosedUnderIsomorphisms

theorem of_iso [P.IsClosedUnderIsomorphisms] {Y : C} (e : X ≅ Y)
    (hX : P.hasFiniteResolution X) : P.hasFiniteResolution Y :=
  P.hasFiniteResolution.prop_of_iso e hX

theorem of_shortExact {S : ShortComplex C} (hS : S.ShortExact) (h₂ : P S.X₂)
    (h₁ : P.hasFiniteResolution S.X₁) : P.hasFiniteResolution S.X₃ := by
  obtain ⟨n, h₁⟩ := hasFiniteResolution_iff.mp h₁
  exact hasFiniteResolutionOfLength.le_hasFiniteResolution _ (.succ S n hS h₂ h₁)

theorem map_exactFunctor {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
    {Q : ObjectProperty D} (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (hF : P ≤ Q.inverseImage F) :
    P.hasFiniteResolution ≤ Q.hasFiniteResolution.inverseImage F := by
  intro X hX
  obtain ⟨n, hX⟩ := hasFiniteResolution_iff.mp hX
  exact hasFiniteResolutionOfLength.le_hasFiniteResolution _
    (hasFiniteResolutionOfLength.map_exactFunctor F hF X hX)

end hasFiniteResolution

end CategoryTheory.ObjectProperty
