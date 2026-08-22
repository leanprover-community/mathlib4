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

* `CategoryTheory.ObjectProperty.HasFiniteResolutionOfLength`:
  We say that `X : C` has a `P`-resolution of length `n` if there exists an
  exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ X ⟶ 0` such that each `Eᵢ : C` satisfies `P`.
* `CategoryTheory.ObjectProperty.HasFiniteResolution`:
  We say that `X : C` has a finite `P`-resolution if it has a `P`-resolution of some finite length.

## Implementation notes

Rather than defining `HasFiniteResolutionOfLength` in terms of explicit exact sequences,
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

Rather than defining `HasFiniteResolutionOfLength` in terms of explicit exact sequences,
we define it inductively: `X` has a `P`-resolution of length `0` if `X` satisfies `P`, and
it has a `P`-resolution of length `n + 1` if there exists a short exact sequence
`0 ⟶ K ⟶ E ⟶ X ⟶ 0` such that `E` satisfies `P` and `K` has a `P`-resolution of length `n`. -/
inductive HasFiniteResolutionOfLength (P : ObjectProperty C) : C → ℕ → Prop
  | zero (X : C) (hX : P X) : HasFiniteResolutionOfLength P X 0
  | succ (S : ShortComplex C) (n : ℕ) (hS : S.ShortExact) (h₂ : P S.X₂)
      (h₁ : HasFiniteResolutionOfLength P S.X₁ n) : HasFiniteResolutionOfLength P S.X₃ (n + 1)

/-- Let `C` be a category, `P : ObjectProperty C` be a property of objects in `C`.
We say that `X : C` has a finite `P`-resolution if it has a `P`-resolution of some finite length. -/
class HasFiniteResolution (P : ObjectProperty C) (X : C) : Prop where
  out (P X) : ∃ n : ℕ, P.HasFiniteResolutionOfLength X n

variable {P Q : ObjectProperty C} {X : C} {n : ℕ}

namespace HasFiniteResolutionOfLength

theorem property (hX : P.HasFiniteResolutionOfLength X 0) : P X := by
  cases hX with
  | zero _ hX => exact hX

theorem monotone (hPQ : P ≤ Q) (hX : P.HasFiniteResolutionOfLength X n) :
    Q.HasFiniteResolutionOfLength X n := by
  induction hX with
  | zero X hX => exact HasFiniteResolutionOfLength.zero X (hPQ X hX)
  | succ S n hS h₂ _ ih => exact HasFiniteResolutionOfLength.succ S n hS (hPQ S.X₂ h₂) ih

theorem property_of_isClosedUnderQuotients [P.IsClosedUnderQuotients]
    (hX : P.HasFiniteResolutionOfLength X n) : P X := by
  cases hX with
  | zero _ hX => exact hX
  | succ S _ hS h₂ _ => exact P.prop_X₃_of_shortExact hS h₂

theorem of_iso [P.IsClosedUnderIsomorphisms] {Y : C} (e : X ≅ Y)
    (hX : P.HasFiniteResolutionOfLength X n) : P.HasFiniteResolutionOfLength Y n := by
  cases hX with
  | zero _ hX => exact HasFiniteResolutionOfLength.zero Y (P.prop_of_iso e hX)
  | succ S n hS h₂ h₁ =>
      let T : ShortComplex C := ShortComplex.mk S.f (S.g ≫ e.hom) (by simp)
      let eS : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp [T]) (by simp [T])
      exact HasFiniteResolutionOfLength.succ T n (ShortComplex.shortExact_of_iso eS hS) h₂ h₁

theorem map_exactFunctor {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
    {Q : ObjectProperty D} (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : P ≤ Q.inverseImage F) (hX : P.HasFiniteResolutionOfLength X n) :
    Q.HasFiniteResolutionOfLength (F.obj X) n := by
  induction hX with
  | zero X hX =>
      exact HasFiniteResolutionOfLength.zero (F.obj X) (hF X hX)
  | succ S n hS h₂ _ ih =>
      exact HasFiniteResolutionOfLength.succ (S.map F) n (hS.map_of_exact F) (hF S.X₂ h₂) ih

theorem hasFiniteResolution (hX : P.HasFiniteResolutionOfLength X n) : P.HasFiniteResolution X :=
  ⟨n, hX⟩

end HasFiniteResolutionOfLength

namespace HasFiniteResolution

theorem of_property (hX : P X) : P.HasFiniteResolution X :=
  ⟨0, HasFiniteResolutionOfLength.zero X hX⟩

instance [P.Is X] : P.HasFiniteResolution X :=
  of_property (P.prop_of_is X)

theorem monotone (hPQ : P ≤ Q) [P.HasFiniteResolution X] : Q.HasFiniteResolution X := by
  obtain ⟨_, hX⟩ := HasFiniteResolution.out P X
  exact (hX.monotone hPQ).hasFiniteResolution

theorem property_of_isClosedUnderQuotients [P.IsClosedUnderQuotients] [P.HasFiniteResolution X] :
    P X := by
  obtain ⟨_, hX⟩ := HasFiniteResolution.out P X
  exact hX.property_of_isClosedUnderQuotients

theorem of_iso [P.IsClosedUnderIsomorphisms] [P.HasFiniteResolution X] {Y : C} (e : X ≅ Y) :
    P.HasFiniteResolution Y := by
  obtain ⟨_, hX⟩ := HasFiniteResolution.out P X
  exact (hX.of_iso e).hasFiniteResolution

theorem of_shortExact {S : ShortComplex C} (hS : S.ShortExact) (h₂ : P S.X₂)
    [P.HasFiniteResolution S.X₁] : P.HasFiniteResolution S.X₃ := by
  obtain ⟨n, h₁⟩ := HasFiniteResolution.out P S.X₁
  exact (HasFiniteResolutionOfLength.succ S n hS h₂ h₁).hasFiniteResolution

theorem map_exactFunctor {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
    {Q : ObjectProperty D} (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : P ≤ Q.inverseImage F) [P.HasFiniteResolution X] :
    Q.HasFiniteResolution (F.obj X) := by
  obtain ⟨_, hX⟩ := HasFiniteResolution.out P X
  exact (hX.map_exactFunctor F hF).hasFiniteResolution

end HasFiniteResolution

end CategoryTheory.ObjectProperty
