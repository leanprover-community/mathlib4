/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Generator.StrongGenerator
public import Mathlib.LinearAlgebra.Span.Basic

import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# As a module over itself, a ring is a strong generator

If `R` is a ring, we show that as a ring over itself,
`R` is a strong generator of the category `ModuleCat R`.

-/

public section

open CategoryTheory Opposite

universe w

namespace ModuleCat

variable (R : Type w) [Ring R]

/-- The forget functor `ModuleCat R ⥤ Type _` is corepresentable by `R` as a module over itself. -/
@[expose, simps! +dsimpLhs]
def corepresentableByForget : (forget (ModuleCat.{w} R)).CorepresentableBy (.of R R) where
  homEquiv :=
    { toFun f := f.hom 1
      invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
      left_inv _ := by cat_disch
      right_inv _ := by simp }

/-- The forget functor `ModuleCat R ⥤ Type _` is corepresentable by `R` as a module over itself. -/
@[expose, simps! +dsimpLhs]
def coyonedaObjIsoForget : coyoneda.obj (op (ModuleCat.of R R)) ≅ forget _ :=
  NatIso.ofComponents (fun M ↦ (corepresentableByForget R).homEquiv.toIso)

lemma isSeparating_singleton :
    (ObjectProperty.singleton (ModuleCat.of R R)).IsSeparating := by
  intro _ _ _ _ h
  ext m
  simpa using congr($(h _ ⟨⟨⟩⟩ ((corepresentableByForget R).homEquiv.symm m)) 1)

lemma isStrongGenerator_singleton :
    (ObjectProperty.singleton (ModuleCat.of R R)).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨isSeparating_singleton R, ?_⟩
  rintro M N i _ hi
  have : Epi i := by
    rw [epi_iff_surjective]
    intro n
    obtain ⟨f, hf⟩ := hi _ ⟨⟨⟩⟩ ((corepresentableByForget R).homEquiv.symm n)
    obtain ⟨m, rfl⟩ := (corepresentableByForget R).homEquiv.symm.surjective f
    exact ⟨m, by simpa using congr($(hf) 1)⟩
  exact Balanced.isIso_of_mono_of_epi i

end ModuleCat
