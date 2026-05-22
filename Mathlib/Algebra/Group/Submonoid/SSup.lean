/-
Copyright (c) 2024 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Zibrowius
-/
module

public import Mathlib.Algebra.Group.Submonoid.Basic

/-! # Suprema in a SubmonoidClass -/

public section

open Submonoid in
/-- A class to indicate that the canonical map `.ofClass` from a class `S` of submonoids
    of `M` to `Submonoid M` preserves suprema. -/
class SubmonoidClass.IsConcreteSSup (S : Type*) (M : outParam Type*) [Monoid M] [SetLike S M]
    [SubmonoidClass S M] [SupSet S] : Prop where
  sSup_toSubmonoid (S : Set S) : ofClass (sSup S) = sSup (ofClass '' S)

open AddSubmonoid in
/-- A class to indicate that the canonical map `.ofClass` from a class `S` of additive submonoids
    of `M` to `AddSubmonoid M` preserves suprema. -/
class AddSubmonoidClass.IsConcreteSSup (S : Type*) (M : outParam Type*) [AddMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] [SupSet S] : Prop where
  sSup_toAddSubmonoid (S : Set S) : ofClass (sSup S) = sSup (ofClass '' S)

attribute [to_additive existing] SubmonoidClass.IsConcreteSSup

namespace SubmonoidClass

open Submonoid

@[to_additive]
theorem iSup_toSubmonoid {S : Type*} {M : Type*} [SetLike S M] [Monoid M] [SubmonoidClass S M]
    [SupSet S] [IsConcreteSSup S M]
    {ι : Sort*} (ℳ : ι → S) :
    ofClass (⨆ i, ℳ i) = ⨆ i, ofClass (ℳ i) := by
  rw [iSup,IsConcreteSSup.sSup_toSubmonoid,←Set.range_comp]
  rfl

@[to_additive, simp]
theorem mem_iSup_iff_mem_iSup_Submonoid {S : Type*} {M : Type*} [SetLike S M] [Monoid M]
    [SubmonoidClass S M] [SupSet S] [IsConcreteSSup S M] {ι : Sort*} (ℳ : ι → S) (m : M) :
    m ∈ (⨆ i, ℳ i : S) ↔ m ∈ (⨆ i, ofClass (ℳ i)) := by
  rw [← iSup_toSubmonoid ℳ]
  rfl

@[to_additive]
instance (M : Type*) [Monoid M] : IsConcreteSSup (Submonoid M) M where
  sSup_toSubmonoid S := by
    have : ofClass (sSup S) = sSup S := by rfl
    rw [this, Set.EqOn.image_eq_self (f := ofClass) (fun _ ↦ congrFun rfl)]

end SubmonoidClass
