/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.Algebra.Exact
import Mathlib.CategoryTheory.Category.Pointed.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exactness in the category of pointed types

In this file we prove some basic results about exactness in the category of pointed types

-/
open CategoryTheory

universe u

namespace Pointed

instance : Limits.HasZeroMorphisms Pointed.{u} where
  zero _ Y := ⟨⟨fun _ ↦ Y.point, rfl⟩⟩
  comp_zero _ _ := ConcreteCategory.ext (Subtype.ext (funext fun _ ↦ rfl))
  zero_comp _ _ _ f  := ConcreteCategory.ext (Subtype.ext (funext fun _ ↦ f.map_point))

section exact

theorem mono_iff_injective {X Y : Pointed.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := sorry

theorem epi_iff_surjective {X Y : Pointed.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := sorry

theorem shortComplex_exact_iff (S : ShortComplex Pointed.{u}) :
    S.Exact ↔ ∀ (x : S.X₂), S.g x = S.X₃.point → x ∈ Set.range S.f := sorry

theorem shortComplex_exact_iff_exact (S : ShortComplex Pointed.{u}) [Zero S.X₃]
    (h : S.X₃.point = 0) : S.Exact ↔ Function.Exact S.f S.g := sorry

end exact

end Pointed
