/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Edison Xie
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Subobject

/-! # Short Exact Sequences in Abelian Categories

This file contains lemmas about short exact sequences in abelian categories.

-/

public section

namespace CategoryTheory.ShortExact

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits Preadditive CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F] [F.Faithful]
variable {S : ShortComplex C}

lemma reflects_shortExact_of_faithful (hS : (S.map F).ShortExact) : S.ShortExact where
  exact := F.reflects_exact_of_faithful _ hS.1
  mono_f := ReflectsMonomorphisms.reflects _ hS.mono_f
  epi_g := ReflectsEpimorphisms.reflects _ hS.epi_g

lemma shortExact_map_iff [PreservesFiniteColimits F] [PreservesFiniteLimits F] :
    (S.map F).ShortExact ↔ S.ShortExact :=
  ⟨reflects_shortExact_of_faithful F, fun h ↦ ShortComplex.ShortExact.map_of_exact h F⟩

end CategoryTheory.ShortExact

namespace CategoryTheory.Abelian

open Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

section

variable {X Y : C} {A : Subobject X} (f : X ⟶ Y) [Epi f] (B : Subobject Y)
  (h : A.arrow ≫ f = 0)

/-- For an epimorphism `f : X ⟶ Y`, a subobject `A` of `X` with `A.arrow ≫ f = 0` and a
subobject `B` of `Y`, this is the short complex
`A ⟶ (Subobject.pullback f).obj B ⟶ B`, whose first map is the canonical inclusion and
whose second map is `Subobject.pullbackπ`. -/
@[expose]
noncomputable def shortComplexPullbackπ : ShortComplex C :=
  ShortComplex.mk _ _ (Subobject.ofLE_comp_pullbackπ_eq_zero f B h)

/-- If moreover `A.arrow` is a kernel of `f`, the short complex
`A ⟶ (Subobject.pullback f).obj B ⟶ B` is short exact; that is, the pullback of `B` along `f`
is an extension of `B` by `A`. -/
lemma shortExact_shortComplexPullbackπ (hA : IsLimit (KernelFork.ofι A.arrow h)) :
    (shortComplexPullbackπ f B h).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (Subobject.isLimitKernelForkPullbackπ f B h hA)
  mono_f := by dsimp [shortComplexPullbackπ]; infer_instance
  epi_g := by dsimp [shortComplexPullbackπ]; infer_instance

end

section

variable {X : C} {A : Subobject X} (B : Subobject (cokernel A.arrow))

/-- Given a subobject `A` of `X` and a subobject `B` of `cokernel A.arrow`, the short complex
`A ⟶ (Subobject.pullback (cokernel.π A.arrow)).obj B ⟶ B`. -/
@[expose]
noncomputable def shortComplexPullbackπCokernelπ : ShortComplex C :=
  shortComplexPullbackπ (cokernel.π A.arrow) B (cokernel.condition _)

/-- The pullback of `B : Subobject (cokernel A.arrow)` along `cokernel.π A.arrow` is an
extension of `B` by `A`; this is the correspondence between subobjects of `X` containing `A`
and subobjects of the quotient. -/
lemma shortExact_shortComplexPullbackπCokernelπ :
    (shortComplexPullbackπCokernelπ B).ShortExact :=
  shortExact_shortComplexPullbackπ _ B _
    (monoIsKernelOfCokernel (CokernelCofork.ofπ (cokernel.π A.arrow) (cokernel.condition A.arrow))
      (cokernelIsCokernel A.arrow))

end

end CategoryTheory.Abelian
