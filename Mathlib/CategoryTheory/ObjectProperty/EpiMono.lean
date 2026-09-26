/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Properties of objects that are closed under subobjects and quotients

Given a category `C` and `P : ObjectProperty C`, we define type classes
`P.IsClosedUnderSubobjects` and `P.IsClosedUnderQuotients` expressing
that `P` is closed under subobjects (resp. quotients).

We also relate these two classes to their analogues in the opposite category:
`P.op` is closed under quotients iff `P` is closed under subobjects, and dually.

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- Given `P : ObjectProperty C`, we say that `P` is closed under subobjects,
if for any monomorphism `X ⟶ Y`, `P Y` implies `P X`. -/
class IsClosedUnderSubobjects : Prop where
  prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X

section

variable [P.IsClosedUnderSubobjects]

lemma prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X :=
  IsClosedUnderSubobjects.prop_of_mono f hY

instance : P.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_mono e.inv

lemma prop_X₁_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₁ := by
  have := hS.mono_f
  exact P.prop_of_mono S.f h₂

instance (F : D ⥤ C) [F.PreservesMonomorphisms] :
    (P.inverseImage F).IsClosedUnderSubobjects where
  prop_of_mono f _ h := P.prop_of_mono (F.map f) h

instance {ι : Type*} (P : ι → ObjectProperty C) [∀ i, (P i).IsClosedUnderSubobjects] :
    (⨆ i, P i).IsClosedUnderSubobjects where
  prop_of_mono f _ h := by
    simp only [prop_iSup_iff] at h ⊢
    obtain ⟨i, hi⟩ := h
    exact ⟨i, (P i).prop_of_mono f hi⟩

end

section

/-- Given `P : ObjectProperty C`, we say that `P` is closed under quotients,
if for any epimorphism `X ⟶ Y`, `P X` implies `P Y`. -/
class IsClosedUnderQuotients : Prop where
  prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y

variable [P.IsClosedUnderQuotients]

lemma prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y :=
  IsClosedUnderQuotients.prop_of_epi f hX

instance : P.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_epi e.hom

lemma prop_X₃_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₃ := by
  have := hS.epi_g
  exact P.prop_of_epi S.g h₂

instance (F : D ⥤ C) [F.PreservesEpimorphisms] :
    (P.inverseImage F).IsClosedUnderQuotients where
  prop_of_epi f _ h := P.prop_of_epi (F.map f) h

instance {ι : Type*} (P : ι → ObjectProperty C) [∀ i, (P i).IsClosedUnderQuotients] :
    (⨆ i, P i).IsClosedUnderQuotients where
  prop_of_epi f _ h := by
    simp only [prop_iSup_iff] at h ⊢
    obtain ⟨i, hi⟩ := h
    exact ⟨i, (P i).prop_of_epi f hi⟩

end

instance : (⊤ : ObjectProperty C).IsClosedUnderSubobjects where
  prop_of_mono := by simp

instance : (⊤ : ObjectProperty C).IsClosedUnderQuotients where
  prop_of_epi := by simp

instance [HasZeroMorphisms C] : IsClosedUnderSubobjects (IsZero (C := C)) where
  prop_of_mono f _ hX := IsZero.of_mono f hX

instance [HasZeroMorphisms C] : IsClosedUnderQuotients (IsZero (C := C)) where
  prop_of_epi f _ hX := IsZero.of_epi f hX

section Opposite

/-- A property of objects `P.op` is closed under quotients iff `P` is closed under
subobjects, since epimorphisms in `Cᵒᵖ` correspond to monomorphisms in `C`. -/
lemma isClosedUnderQuotients_op_iff :
    P.op.IsClosedUnderQuotients ↔ P.IsClosedUnderSubobjects :=
  ⟨fun h ↦ ⟨fun i _ hY ↦ h.prop_of_epi i.op hY⟩,
    fun h ↦ ⟨fun f _ hA ↦ h.prop_of_mono f.unop hA⟩⟩

/-- A property of objects `P.op` is closed under subobjects iff `P` is closed under
quotients, since monomorphisms in `Cᵒᵖ` correspond to epimorphisms in `C`. -/
lemma isClosedUnderSubobjects_op_iff :
    P.op.IsClosedUnderSubobjects ↔ P.IsClosedUnderQuotients :=
  ⟨fun h ↦ ⟨fun f _ hX ↦ h.prop_of_mono f.op hX⟩,
    fun h ↦ ⟨fun i _ hB ↦ h.prop_of_epi i.unop hB⟩⟩

instance [P.IsClosedUnderSubobjects] : P.op.IsClosedUnderQuotients := by
  rwa [isClosedUnderQuotients_op_iff]

instance [P.IsClosedUnderQuotients] : P.op.IsClosedUnderSubobjects := by
  rwa [isClosedUnderSubobjects_op_iff]

variable (Q : ObjectProperty Cᵒᵖ)

/-- A property of objects `Q.unop` is closed under quotients iff `Q` is closed under
subobjects. -/
lemma isClosedUnderQuotients_unop_iff :
    Q.unop.IsClosedUnderQuotients ↔ Q.IsClosedUnderSubobjects :=
  Q.unop.isClosedUnderSubobjects_op_iff.symm

/-- A property of objects `Q.unop` is closed under subobjects iff `Q` is closed under
quotients. -/
lemma isClosedUnderSubobjects_unop_iff :
    Q.unop.IsClosedUnderSubobjects ↔ Q.IsClosedUnderQuotients :=
  Q.unop.isClosedUnderQuotients_op_iff.symm

instance [Q.IsClosedUnderSubobjects] : Q.unop.IsClosedUnderQuotients := by
  rwa [isClosedUnderQuotients_unop_iff]

instance [Q.IsClosedUnderQuotients] : Q.unop.IsClosedUnderSubobjects := by
  rwa [isClosedUnderSubobjects_unop_iff]

end Opposite

end ObjectProperty

end CategoryTheory
