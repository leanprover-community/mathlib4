/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Finite resolutions by objects satisfying `P : ObjectProperty A`

## Main definitions

Let `A` be a category with zero morphisms, `P : ObjectProperty A` be a property of objects in `A`.

* `CategoryTheory.ObjectProperty.HasFiniteResolutionOfLength`:
  We say that `X : A` has a `P`-resolution of length `n` if there exists an
  exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ X ⟶ 0` such that each `Eᵢ : A` satisfies `P`.
* `CategoryTheory.ObjectProperty.HasFiniteResolution`:
  We say that `X : A` has a finite `P`-resolution if it has a `P`-resolution of some finite length.
-/

public section

universe v' v u' u

namespace CategoryTheory.ObjectProperty

open Limits

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- Let `A` be a category with zero morphisms, `P : ObjectProperty A` be a property of objects
in `A`. We say that `X : A` has a `P`-resolution of length `n` if there exists an
exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ X ⟶ 0` such that each `Eᵢ : A` satisfies `P`. -/
inductive HasFiniteResolutionOfLength (P : ObjectProperty A) : A → ℕ → Prop
  | zero (X : A) (hX : P X) : HasFiniteResolutionOfLength P X 0
  | succ (S : ShortComplex A) (n : ℕ) (hS : S.ShortExact) (h₂ : P S.X₂)
      (h₁ : HasFiniteResolutionOfLength P S.X₁ n) : HasFiniteResolutionOfLength P S.X₃ (n + 1)

/-- Let `A` be a category with zero morphisms, `P : ObjectProperty A` be a property of objects
in `A`. We say that `X : A` has a finite `P`-resolution if it has a `P`-resolution of some finite
length. -/
class HasFiniteResolution (P : ObjectProperty A) (X : A) : Prop where
  out (P X) : ∃ n : ℕ, P.HasFiniteResolutionOfLength X n

variable {P Q : ObjectProperty A} {X : A} {n : ℕ}

namespace HasFiniteResolutionOfLength

theorem property_of_zero (hX : P.HasFiniteResolutionOfLength X 0) : P X := by
  cases hX with
  | zero _ hX => exact hX

theorem mono (hPQ : P ≤ Q) (hX : P.HasFiniteResolutionOfLength X n) :
    Q.HasFiniteResolutionOfLength X n := by
  induction hX with
  | zero X hX => exact HasFiniteResolutionOfLength.zero X (hPQ X hX)
  | succ S n hS h₂ _ ih => exact HasFiniteResolutionOfLength.succ S n hS (hPQ S.X₂ h₂) ih

theorem property [P.IsClosedUnderQuotients] (hX : P.HasFiniteResolutionOfLength X n) : P X := by
  cases hX with
  | zero _ hX => exact hX
  | succ S _ hS h₂ _ => exact P.prop_X₃_of_shortExact hS h₂

theorem property_of_le [Q.IsClosedUnderQuotients] (hPQ : P ≤ Q)
    (hX : P.HasFiniteResolutionOfLength X n) : Q X :=
  (hX.mono hPQ).property

theorem of_iso [P.IsClosedUnderIsomorphisms] {Y : A} (e : X ≅ Y)
    (hX : P.HasFiniteResolutionOfLength X n) : P.HasFiniteResolutionOfLength Y n := by
  cases hX with
  | zero _ hX => exact HasFiniteResolutionOfLength.zero Y (P.prop_of_iso e hX)
  | succ S n hS h₂ h₁ =>
      let T : ShortComplex A := ShortComplex.mk S.f (S.g ≫ e.hom) (by simp)
      let eS : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp [T]) (by simp [T])
      exact HasFiniteResolutionOfLength.succ T n (ShortComplex.shortExact_of_iso eS hS) h₂ h₁

theorem map_exactFunctor {B : Type u'} [Category.{v'} B] [HasZeroMorphisms B]
    {Q : ObjectProperty B} (F : A ⥤ B) [F.PreservesZeroMorphisms]
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

protected theorem elim [P.HasFiniteResolution X] {Q : Prop}
    (h : ∀ n, P.HasFiniteResolutionOfLength X n → Q) : Q :=
  Exists.elim (HasFiniteResolution.out P X) h

theorem mono (hPQ : P ≤ Q) [P.HasFiniteResolution X] : Q.HasFiniteResolution X :=
  HasFiniteResolution.elim fun _ hX ↦ (hX.mono hPQ).hasFiniteResolution

theorem property_of_le [Q.IsClosedUnderQuotients] (hPQ : P ≤ Q) [P.HasFiniteResolution X] : Q X :=
  HasFiniteResolution.elim fun _ hX ↦ hX.property_of_le hPQ

theorem property [P.IsClosedUnderQuotients] [P.HasFiniteResolution X] : P X :=
  property_of_le (le_refl P)

theorem of_iso [P.IsClosedUnderIsomorphisms] [P.HasFiniteResolution X] {Y : A} (e : X ≅ Y) :
    P.HasFiniteResolution Y :=
  HasFiniteResolution.elim fun _ hX ↦ (hX.of_iso e).hasFiniteResolution

theorem of_shortExact {S : ShortComplex A} (hS : S.ShortExact) (h₂ : P S.X₂)
    [P.HasFiniteResolution S.X₁] : P.HasFiniteResolution S.X₃ :=
  HasFiniteResolution.elim fun n h₁ ↦
    (HasFiniteResolutionOfLength.succ S n hS h₂ h₁).hasFiniteResolution

theorem map_exactFunctor {B : Type u'} [Category.{v'} B] [HasZeroMorphisms B]
    {Q : ObjectProperty B} (F : A ⥤ B) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : P ≤ Q.inverseImage F) [P.HasFiniteResolution X] :
    Q.HasFiniteResolution (F.obj X) :=
  HasFiniteResolution.elim fun _ hX ↦ (hX.map_exactFunctor F hF).hasFiniteResolution

end HasFiniteResolution

end CategoryTheory.ObjectProperty
