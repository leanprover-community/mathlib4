/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Closure properties of orthogonals

Let `P` be a property of objects in a category with zero morphisms. We show that the left
orthogonal `P.leftOrthogonal` is closed under quotients and under colimits of any shape, and,
dually, that the right orthogonal `P.rightOrthogonal` is closed under subobjects and under
limits of any shape. These are registered as instances of `IsClosedUnderQuotients`,
`IsClosedUnderColimitsOfShape`, `IsClosedUnderSubobjects` and `IsClosedUnderLimitsOfShape`.

We also relate the closure properties of `P` to those of `P.op`: closure under subobjects
corresponds to closure under quotients in the opposite category, and closure under extensions
is self-dual.

## Main results

* `CategoryTheory.ObjectProperty.isClosedUnderQuotients_op_iff`: `P.op` is closed under
  quotients iff `P` is closed under subobjects.
* `CategoryTheory.ObjectProperty.isClosedUnderExtensions_op_iff`: `P.op` is closed under
  extensions iff `P` is.
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- The left orthogonal of a property of objects is closed under quotients. -/
instance (P : ObjectProperty C) : P.leftOrthogonal.IsClosedUnderQuotients where
  prop_of_epi f _ hX := (P.leftOrthogonal_iff _).mpr
    fun _ g hZ ↦ zero_of_epi_comp f (hX (f ≫ g) hZ)

/-- The left orthogonal of a property of objects is closed under colimits of any shape. -/
instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isColimit.hom_ext
    intro j
    simp only [comp_zero]
    exact hX.prop_diag_obj j (hX.ι.app j ≫ f) hY

/-- The right orthogonal of a property of objects is closed under subobjects. -/
instance (P : ObjectProperty C) : P.rightOrthogonal.IsClosedUnderSubobjects where
  prop_of_mono i _ hY := (P.rightOrthogonal_iff _).mpr
    fun _ f hX ↦ zero_of_comp_mono i (hY (f ≫ i) hX)

/-- The right orthogonal of a property of objects is closed under limits of any shape. -/
instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    P.rightOrthogonal.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isLimit.hom_ext
    intro j
    simp only [zero_comp]
    exact hX.prop_diag_obj j (f ≫ hX.π.app j) hY

omit [HasZeroMorphisms C] in
/-- A property of objects `P.op` is closed under quotients iff `P` is closed under
subobjects, since epimorphisms in `Cᵒᵖ` correspond to monomorphisms in `C`. -/
lemma isClosedUnderQuotients_op_iff (P : ObjectProperty C) :
    P.op.IsClosedUnderQuotients ↔ P.IsClosedUnderSubobjects :=
  ⟨fun h ↦ ⟨fun i _ hY ↦ h.prop_of_epi i.op hY⟩,
    fun h ↦ ⟨fun f _ hA ↦ h.prop_of_mono f.unop hA⟩⟩

/-- A property of objects `P.op` is closed under extensions iff `P` is, since a short
complex in `Cᵒᵖ` is short exact iff the corresponding short complex in `C` is. -/
lemma isClosedUnderExtensions_op_iff (P : ObjectProperty C) :
    P.op.IsClosedUnderExtensions ↔ P.IsClosedUnderExtensions :=
  ⟨fun h ↦ ⟨fun hS h₁ h₃ ↦ h.prop_X₂_of_shortExact hS.op h₃ h₁⟩,
    fun h ↦ ⟨fun hS h₁ h₃ ↦ h.prop_X₂_of_shortExact hS.unop h₃ h₁⟩⟩

end HasZeroMorphisms


/-! Closure under extensions uses the kernel and cokernel supplied by a short exact sequence, so
these two instances are stated for preadditive balanced categories. -/

section Extensions

variable [Preadditive C] [Balanced C]

/-- The left orthogonal of a property of objects is closed under extensions. -/
instance (P : ObjectProperty C) : P.leftOrthogonal.IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    intro s hs hX₁ hX₃ Z k hZ
    let t : CokernelCofork s.f := CokernelCofork.ofπ k (hX₁ (s.f ≫ k) hZ)
    let l : s.X₃ ⟶ Z := hs.gIsCokernel.desc t
    have hl : l = 0 := hX₃ l hZ
    have hfac : s.g ≫ l = k := hs.gIsCokernel.fac t WalkingParallelPair.one
    simp [← hfac, hl]

/-- The right orthogonal of a property of objects is closed under extensions. -/
instance (P : ObjectProperty C) : P.rightOrthogonal.IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    intro s hs hX₁ hX₃ Z k hZ
    let t : KernelFork s.g := KernelFork.ofι k (hX₃ (k ≫ s.g) hZ)
    let l : Z ⟶ s.X₁ := hs.fIsKernel.lift t
    have hl : l = 0 := hX₁ l hZ
    have hfac : l ≫ s.f = k := hs.fIsKernel.fac t WalkingParallelPair.zero
    simp [← hfac, hl]

end Extensions

end ObjectProperty

end CategoryTheory
