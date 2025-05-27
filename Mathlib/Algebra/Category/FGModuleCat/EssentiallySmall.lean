/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The category of finitely generated modules over a ring is essentially small

This file proves that `FGModuleCat R`, the category of finitely generated modules over a ring `R`,
is essentially small, by providing an explicit small model. However, for applications, it is
recommended to use the standard `CategoryTheory.SmallModel (FGModuleCat R)` instead.

-/

open CategoryTheory Classical
variable (R : Type u) [CommRing R]

/-- A (category-theoretically) small version of `FGModuleCat R`. This is used to prove that
`FGModuleCat R` is essentially small. For actual use, it might be recommended to use the canonical
`CategoryTheory.SmallModel` instead of this construction. -/
structure FGModuleRepr : Type u where
  (n : ℕ)
  (S : Submodule R (Fin n → R))

namespace FGModuleRepr

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

variable {R} in
/-- The finite module represented by an object of the type `FGModuleRepr R`, which is the quotient
of `Fin n → R` (i.e. $$R^n$$) by the submodule `S` provided. -/
def repr (x : FGModuleRepr R) : Type u :=
  _ ⧸ x.S

instance : CoeSort (FGModuleRepr R) (Type u) :=
  ⟨repr⟩

instance addCommGroup (x : FGModuleRepr R) : AddCommGroup x := by
  unfold repr; exact inferInstance

instance module (x : FGModuleRepr R) : Module R x := by
  unfold repr; exact inferInstance

instance finite (x : FGModuleRepr R) : Module.Finite R x := by
  unfold repr; exact inferInstance

/-- A non-canonical representation of a finite module (as a quotient of $$R^n$$). -/
noncomputable def of_finite : FGModuleRepr R where
  n := (Module.Finite.exists_fin_iso R M).choose
  S := (Module.Finite.exists_fin_iso R M).choose_spec.choose

/-- The non-canonical representation `of_finite` of a finite module is actually isomorphic to
the given module. -/
noncomputable def of_finite_iso : of_finite R M ≃ₗ[R] M :=
  choice (Module.Finite.exists_fin_iso R M).choose_spec.choose_spec

instance category : Category (FGModuleRepr R) :=
  CategoryTheory.InducedCategory.category (fun x : FGModuleRepr R ↦ FGModuleCat.of R x)

instance smallCategory : SmallCategory (FGModuleRepr R) where

/-- The canonical embedding of this small category to the canonical (large) category
`FGModuleCat R`. -/
def embed : FGModuleRepr R ⥤ FGModuleCat R :=
  inducedFunctor _

instance : (embed R).IsEquivalence where
  faithful := (fullyFaithfulInducedFunctor _).faithful
  full := (fullyFaithfulInducedFunctor _).full
  essSurj := ⟨fun M ↦ ⟨of_finite R M, ⟨(of_finite_iso R M).toFGModuleCatIso⟩⟩⟩

end FGModuleRepr

instance : EssentiallySmall.{u} (FGModuleCat.{u} R) :=
  ⟨_, _, ⟨(FGModuleRepr.embed R).asEquivalence.symm⟩⟩
